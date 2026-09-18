import Mathlib

/-!
# Compact codec and costed parsers for certificate words

The generic part of the certificate syntax: the unary width prefix and the
compact binary field codec for natural numbers, word lists of compact fields,
the legacy unary codec, the prefix splitter for word lists, and the recursive
decoders that count inspected bit cells. Nothing here mentions a rewrite
system. `RecursorCertificateSyntax` applies the codec to the free-recursor
certificate words; the declarations keep that namespace, so their names are
unchanged.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax

/-- Fixed-width binary payload width convention. This is not by itself a
self-delimiting field encoding. -/
def natBitLength (n : Nat) : Nat := Nat.log 2 n + 1

/-- Number of significant payload bits in the compact encoding of `n`. Encoding
uses the binary digits of `n+1`, so zero also has a one-bit payload. -/
def compactNatPayloadWidth (n : Nat) : Nat := Nat.size (n + 1)

/-- Exact self-delimiting compact field length: a unary pref for the binary
payload width followed by that many binary payload bits. -/
def compactNatFieldBits (n : Nat) : Nat := 2 * compactNatPayloadWidth n + 1

/-- Recursive pref splitter used by the costed parser. -/
def splitPrefixCosted : Nat → List Nat → Option (List Nat × List Nat) × Nat
  | 0, xs => (some ([], xs), 1)
  | _ + 1, [] => (none, 1)
  | n + 1, x :: xs =>
      let r := splitPrefixCosted n xs
      match r.1 with
      | none => (none, r.2 + 1)
      | some (pref, rest) => (some (x :: pref, rest), r.2 + 1)

/-- Prefix splitting agrees with `take` and `drop` when enough words exist. -/
theorem splitPrefixCosted_success (n : Nat) (xs : List Nat)
    (h : n ≤ xs.length) :
    (splitPrefixCosted n xs).1 = some (xs.take n, xs.drop n) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => simp at h
      | cons x xs =>
          have hn : n ≤ xs.length := by simpa using h
          simp only [splitPrefixCosted, List.take_succ_cons, List.drop_succ_cons]
          rw [ih xs hn]

/-- A requested prefix longer than the input is rejected. -/
theorem splitPrefixCosted_none (n : Nat) (xs : List Nat)
    (h : xs.length < n) :
    (splitPrefixCosted n xs).1 = none := by
  induction n generalizing xs with
  | zero => simp at h
  | succ n ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          have hn : xs.length < n := by simpa using h
          simp only [splitPrefixCosted]
          rw [ih xs hn]

/-- Exact successful prefix characterization. -/
theorem splitPrefixCosted_eq_some_iff
    (n : Nat) (xs : List Nat) (pref rest : List Nat) :
    (splitPrefixCosted n xs).1 = some (pref, rest) ↔
      n ≤ xs.length ∧ pref = xs.take n ∧ rest = xs.drop n := by
  constructor
  · intro h
    have hn : n ≤ xs.length := by
      by_contra hnot
      have hlt : xs.length < n := Nat.lt_of_not_ge hnot
      rw [splitPrefixCosted_none n xs hlt] at h
      contradiction
    have hs := splitPrefixCosted_success n xs hn
    rw [hs] at h
    cases h
    exact ⟨hn, rfl, rfl⟩
  · rintro ⟨hn, rfl, rfl⟩
    exact splitPrefixCosted_success n xs hn

/-- Parser work never exceeds the requested prefix length plus one terminating
inspection. -/
theorem splitPrefixCosted_snd_le (n : Nat) (xs : List Nat) :
    (splitPrefixCosted n xs).2 ≤ n + 1 := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => simp [splitPrefixCosted]
      | cons x xs =>
          simp only [splitPrefixCosted]
          have h := ih xs
          cases (splitPrefixCosted n xs).1 <;> simp <;> omega

/-- Prefix work is also bounded by the available input length plus one. -/
theorem splitPrefixCosted_snd_le_length (n : Nat) (xs : List Nat) :
    (splitPrefixCosted n xs).2 ≤ xs.length + 1 := by
  induction n generalizing xs with
  | zero => simp [splitPrefixCosted]
  | succ n ih =>
      cases xs with
      | nil => simp [splitPrefixCosted]
      | cons x xs =>
          simp only [splitPrefixCosted, List.length_cons]
          have h := ih xs
          cases (splitPrefixCosted n xs).1 <;> simp <;> omega

/-! ## Legacy unary field codec and compact binary serialization -/

/-- Legacy unary self-delimiting natural-number code: `n` one bits followed by a zero. This is retained only as a reference codec and is not used by `serializeBits`. -/
def encodeNatBits : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: encodeNatBits n

/-- Prefix parser for the legacy unary natural-number code. -/
def decodeNatBits : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
      match decodeNatBits rest with
      | none => none
      | some (n, tail) => some (n + 1, tail)

/-- Legacy unary parser paired with exact consumed-input accounting. On success
the cost is the consumed pref length; on failure every available bit was inspected. -/
def decodeNatBitsCosted (bits : List Bool) : Option (Nat × List Bool) × Nat :=
  match decodeNatBits bits with
  | none => (none, bits.length)
  | some (n, rest) => (some (n, rest), bits.length - rest.length)

@[simp] theorem decodeNatBitsCosted_fst (bits : List Bool) :
    (decodeNatBitsCosted bits).1 = decodeNatBits bits := by
  unfold decodeNatBitsCosted
  cases decodeNatBits bits <;> rfl

/-- Exact consumed-bit accounting is bounded by the input length. -/
theorem decodeNatBitsCosted_snd_le (bits : List Bool) :
    (decodeNatBitsCosted bits).2 ≤ bits.length := by
  unfold decodeNatBitsCosted
  cases decodeNatBits bits with
  | none => rfl
  | some pair => exact Nat.sub_le _ _

/-- Natural-number pref parsing preserves arbitrary trailing bits. -/
theorem decodeNatBits_encodeNatBits_append (n : Nat) (tail : List Bool) :
    decodeNatBits (encodeNatBits n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodeNatBits, decodeNatBits, ih]

/-- Exact bit length of one legacy unary natural field. -/
@[simp] theorem encodeNatBits_length (n : Nat) :
    (encodeNatBits n).length = n + 1 := by
  induction n <;> simp [encodeNatBits, *]

/-- Concatenated legacy unary natural-word encoding. -/
def encodeWordsBits : List Nat → List Bool
  | [] => []
  | n :: ns => encodeNatBits n ++ encodeWordsBits ns

/-- Decode exactly `count` legacy unary natural-number words and return the unconsumed bit
suffix. -/
def decodeWordsBits : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
      match decodeNatBits bits with
      | none => none
      | some (n, rest) =>
          match decodeWordsBits count rest with
          | none => none
          | some (ns, tail) => some (n :: ns, tail)

/-- Costed decoder for exactly `count` legacy unary encoded words. The cost is
exactly the number of input bit cells consumed on success and the full input
length on failure. -/
def decodeWordsBitsCosted (count : Nat) (bits : List Bool) :
    Option (List Nat × List Bool) × Nat :=
  match decodeWordsBits count bits with
  | none => (none, bits.length)
  | some (words, rest) => (some (words, rest), bits.length - rest.length)

@[simp] theorem decodeWordsBitsCosted_fst (count : Nat) (bits : List Bool) :
    (decodeWordsBitsCosted count bits).1 = decodeWordsBits count bits := by
  unfold decodeWordsBitsCosted
  cases decodeWordsBits count bits <;> rfl

/-- Consumed-input accounting never exceeds the available bitstream. -/
theorem decodeWordsBitsCosted_snd_le (count : Nat) (bits : List Bool) :
    (decodeWordsBitsCosted count bits).2 ≤ bits.length := by
  unfold decodeWordsBitsCosted
  cases decodeWordsBits count bits with
  | none => rfl
  | some pair => exact Nat.sub_le _ _

/-- Legacy-unary word-list pref parsing preserves arbitrary trailing bits. -/
theorem decodeWordsBits_encodeWordsBits_append
    (words : List Nat) (tail : List Bool) :
    decodeWordsBits words.length (encodeWordsBits words ++ tail) = some (words, tail) := by
  induction words with
  | nil => simp [encodeWordsBits, decodeWordsBits]
  | cons n ns ih =>
      simp [encodeWordsBits, decodeWordsBits, List.append_assoc,
        decodeNatBits_encodeNatBits_append, ih]

/-- Exact bit length of a list of legacy-unary natural-number words. -/
theorem encodeWordsBits_length (words : List Nat) :
    (encodeWordsBits words).length = (words.map (fun n => n + 1)).sum := by
  induction words with
  | nil => rfl
  | cons n ns ih => simp [encodeWordsBits, ih]

/-- Unary width pref used only to delimit a compact binary payload. Its input is
a binary width, not the natural-number value being encoded. -/
def encodeCompactWidth : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: encodeCompactWidth n

/-- Decoder for the unary width pref. -/
def decodeCompactWidth : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
      match decodeCompactWidth rest with
      | none => none
      | some (n, tail) => some (n + 1, tail)

@[simp] theorem decodeCompactWidth_encode_append (n : Nat) (tail : List Bool) :
    decodeCompactWidth (encodeCompactWidth n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodeCompactWidth, decodeCompactWidth, ih]

@[simp] theorem encodeCompactWidth_length (n : Nat) :
    (encodeCompactWidth n).length = n + 1 := by
  induction n <;> simp [encodeCompactWidth, *]

/-- Reconstruct a natural number from least-significant-bit-first binary digits. -/
def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.bit b (bitsToNat bs)

@[simp] theorem bitsToNat_bits (n : Nat) : bitsToNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | z => simp [bitsToNat]
  | f b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp [bitsToNat, ih]

/-- Actual binary payload width used by the compact codec. -/
def compactNatWidth (n : Nat) : Nat := (n + 1).bits.length

@[simp] theorem compactNatWidth_eq_payloadWidth (n : Nat) :
    compactNatWidth n = compactNatPayloadWidth n := by
  simpa [compactNatWidth, compactNatPayloadWidth] using Nat.size_eq_bits_len (n + 1)

/-- Self-delimiting compact natural field. The width pref costs `w+1` bits and
the actual binary payload costs `w` bits, where `w = Nat.size (n+1)`. -/
def encodeNatCompact (n : Nat) : List Bool :=
  encodeCompactWidth (compactNatWidth n) ++ (n + 1).bits

/-- Prefix decoder for the compact natural field. Noncanonical all-zero payloads
and truncated payloads are rejected. -/
def decodeNatCompact (bits : List Bool) : Option (Nat × List Bool) :=
  match decodeCompactWidth bits with
  | none => none
  | some (width, rest) =>
      let payload := rest.take width
      let tail := rest.drop width
      if payload.length ≠ width then none
      else
        let value := bitsToNat payload
        if value = 0 then none else some (value - 1, tail)

@[simp] theorem encodeNatCompact_length (n : Nat) :
    (encodeNatCompact n).length = compactNatFieldBits n := by
  unfold encodeNatCompact compactNatFieldBits compactNatPayloadWidth compactNatWidth
  rw [List.length_append, encodeCompactWidth_length, Nat.size_eq_bits_len]
  omega

@[simp] theorem decodeNatCompact_encode_append (n : Nat) (tail : List Bool) :
    decodeNatCompact (encodeNatCompact n ++ tail) = some (n, tail) := by
  unfold encodeNatCompact decodeNatCompact
  rw [List.append_assoc, decodeCompactWidth_encode_append]
  simp [compactNatWidth, bitsToNat_bits]

/-- Concatenated compact natural fields. -/
def encodeWordsCompact : List Nat → List Bool
  | [] => []
  | n :: ns => encodeNatCompact n ++ encodeWordsCompact ns

/-- Decode exactly `count` compact natural fields and preserve the unconsumed
suffix. -/
def decodeWordsCompact : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits =>
      match decodeNatCompact bits with
      | none => none
      | some (n, rest) =>
          match decodeWordsCompact count rest with
          | none => none
          | some (ns, tail) => some (n :: ns, tail)

@[simp] theorem decodeWordsCompact_encode_append
    (words : List Nat) (tail : List Bool) :
    decodeWordsCompact words.length (encodeWordsCompact words ++ tail) = some (words, tail) := by
  induction words with
  | nil => rfl
  | cons n ns ih =>
      simp [encodeWordsCompact, decodeWordsCompact, List.append_assoc,
        decodeNatCompact_encode_append, ih]

@[simp] theorem encodeWordsCompact_length (words : List Nat) :
    (encodeWordsCompact words).length = (words.map compactNatFieldBits).sum := by
  induction words with
  | nil => rfl
  | cons n ns ih => simp [encodeWordsCompact, ih]

/-! ## Recursive compact-bit parser accounting -/

/-- Recursive unary-width parser with an actual bit-inspection count. The count
is produced by the same recursion that produces the parsed width. -/
def decodeCompactWidthRuntimeCosted :
    List Bool → Option (Nat × List Bool) × Nat
  | [] => (none, 0)
  | false :: rest => (some (0, rest), 1)
  | true :: rest =>
      let r := decodeCompactWidthRuntimeCosted rest
      let out := match r.1 with
        | none => none
        | some (n, tail) => some (n + 1, tail)
      (out, r.2 + 1)

/-- Runtime width parsing erases to the accepted width parser. -/
@[simp] theorem decodeCompactWidthRuntimeCosted_fst (bits : List Bool) :
    (decodeCompactWidthRuntimeCosted bits).1 = decodeCompactWidth bits := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b with
      | false => rfl
      | true =>
          simp only [decodeCompactWidthRuntimeCosted, decodeCompactWidth]
          generalize hr : decodeCompactWidthRuntimeCosted rest = r
          rcases r with ⟨result, cost⟩
          have ih' := ih
          rw [hr] at ih'
          change result = decodeCompactWidth rest at ih'
          rw [← ih']

/-- Width-parser bit inspections never exceed the available input. -/
theorem decodeCompactWidthRuntimeCosted_snd_le (bits : List Bool) :
    (decodeCompactWidthRuntimeCosted bits).2 ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;> simp only [decodeCompactWidthRuntimeCosted, List.length_cons] <;> omega

/-- On a successful width parse, the unconsumed suffix plus the actual number
of inspected bit cells is exactly the original input length. -/
theorem decodeCompactWidthRuntimeCosted_success_length
    {bits : List Bool} {width : Nat} {tail : List Bool}
    (h : (decodeCompactWidthRuntimeCosted bits).1 = some (width, tail)) :
    tail.length + (decodeCompactWidthRuntimeCosted bits).2 = bits.length := by
  induction bits generalizing width tail with
  | nil => simp [decodeCompactWidthRuntimeCosted] at h
  | cons b rest ih =>
      cases b with
      | false =>
          simp only [decodeCompactWidthRuntimeCosted] at h ⊢
          cases h
          rfl
      | true =>
          simp only [decodeCompactWidthRuntimeCosted] at h ⊢
          generalize hr : decodeCompactWidthRuntimeCosted rest = r at h ⊢
          rcases r with ⟨result, cost⟩
          cases result with
          | none => simp at h
          | some pair =>
              rcases pair with ⟨n, suffix⟩
              simp only at h
              have hs : (decodeCompactWidthRuntimeCosted rest).1 = some (n, suffix) := by
                rw [hr]
              have hlen := ih hs
              rw [hr] at hlen
              simp only at hlen
              cases h
              simp only [List.length_cons]
              omega

/-- Parse exactly `width` payload bits while reconstructing their LSB-first
natural-number value. The cost counts the consumed payload bit cells and is
computed by the same recursion. -/
def decodePayloadRuntimeCosted :
    Nat → List Bool → Option (Nat × List Bool) × Nat
  | 0, bits => (some (0, bits), 0)
  | _ + 1, [] => (none, 0)
  | n + 1, b :: rest =>
      let r := decodePayloadRuntimeCosted n rest
      let out := match r.1 with
        | none => none
        | some (value, tail) => some (Nat.bit b value, tail)
      (out, r.2 + 1)

/-- Enough input bits give exactly the value of the requested prefix and retain
exactly the unconsumed suffix. -/
theorem decodePayloadRuntimeCosted_success
    (width : Nat) (bits : List Bool) (h : width ≤ bits.length) :
    (decodePayloadRuntimeCosted width bits).1 =
      some (bitsToNat (bits.take width), bits.drop width) := by
  induction width generalizing bits with
  | zero => rfl
  | succ width ih =>
      cases bits with
      | nil => simp at h
      | cons b rest =>
          have hw : width ≤ rest.length := by simpa using h
          simp only [decodePayloadRuntimeCosted, List.take_succ_cons, List.drop_succ_cons]
          rw [ih rest hw]
          rfl

/-- A requested payload wider than the available input is rejected. -/
theorem decodePayloadRuntimeCosted_none
    (width : Nat) (bits : List Bool) (h : bits.length < width) :
    (decodePayloadRuntimeCosted width bits).1 = none := by
  induction width generalizing bits with
  | zero => simp at h
  | succ width ih =>
      cases bits with
      | nil => rfl
      | cons b rest =>
          have hw : rest.length < width := by simpa using h
          simp only [decodePayloadRuntimeCosted]
          rw [ih rest hw]

/-- Payload parsing inspects at most the available bit cells. -/
theorem decodePayloadRuntimeCosted_snd_le_length
    (width : Nat) (bits : List Bool) :
    (decodePayloadRuntimeCosted width bits).2 ≤ bits.length := by
  induction width generalizing bits with
  | zero => simp [decodePayloadRuntimeCosted]
  | succ width ih =>
      cases bits with
      | nil => rfl
      | cons b rest =>
          simp only [decodePayloadRuntimeCosted, List.length_cons]
          have h := ih rest
          omega

/-- On any successful payload parse, the output suffix and inspected-bit count
partition the original input exactly. -/
theorem decodePayloadRuntimeCosted_success_length
    {width : Nat} {bits : List Bool} {value : Nat} {tail : List Bool}
    (h : (decodePayloadRuntimeCosted width bits).1 = some (value, tail)) :
    tail.length + (decodePayloadRuntimeCosted width bits).2 = bits.length := by
  induction width generalizing bits value tail with
  | zero =>
      simp only [decodePayloadRuntimeCosted] at h ⊢
      cases h
      omega
  | succ width ih =>
      cases bits with
      | nil => simp [decodePayloadRuntimeCosted] at h
      | cons b rest =>
          simp only [decodePayloadRuntimeCosted] at h ⊢
          generalize hr : decodePayloadRuntimeCosted width rest = r at h ⊢
          rcases r with ⟨result, cost⟩
          cases result with
          | none => simp at h
          | some pair =>
              rcases pair with ⟨n, suffix⟩
              simp only at h
              have hs : (decodePayloadRuntimeCosted width rest).1 = some (n, suffix) := by
                rw [hr]
              have hlen := ih hs
              rw [hr] at hlen
              simp only at hlen
              cases h
              simp only [List.length_cons]
              omega

/-- One-pass compact-natural parser with actual bit-inspection accounting. -/
def decodeNatCompactRuntimeCosted
    (bits : List Bool) : Option (Nat × List Bool) × Nat :=
  let widthResult := decodeCompactWidthRuntimeCosted bits
  match widthResult.1 with
  | none => (none, widthResult.2)
  | some (width, rest) =>
      let payloadResult := decodePayloadRuntimeCosted width rest
      let out := match payloadResult.1 with
        | none => none
        | some (value, tail) => if value = 0 then none else some (value - 1, tail)
      (out, widthResult.2 + payloadResult.2)

/-- The runtime compact-natural parser has exactly the accepted parser semantics. -/
@[simp] theorem decodeNatCompactRuntimeCosted_fst (bits : List Bool) :
    (decodeNatCompactRuntimeCosted bits).1 = decodeNatCompact bits := by
  unfold decodeNatCompactRuntimeCosted decodeNatCompact
  generalize hw : decodeCompactWidthRuntimeCosted bits = widthResult
  rcases widthResult with ⟨widthOption, widthCost⟩
  have hwfst := decodeCompactWidthRuntimeCosted_fst bits
  rw [hw] at hwfst
  change widthOption = decodeCompactWidth bits at hwfst
  rw [← hwfst]
  cases widthOption with
  | none => rfl
  | some pair =>
      rcases pair with ⟨width, rest⟩
      simp only
      by_cases hlen : width ≤ rest.length
      · rw [decodePayloadRuntimeCosted_success width rest hlen]
        have htake : (rest.take width).length = width := by
          simp [List.length_take, hlen]
        simp [htake]
      · have hlt : rest.length < width := Nat.lt_of_not_ge hlen
        rw [decodePayloadRuntimeCosted_none width rest hlt]
        simp [List.length_take, hlen]

/-- Compact-natural parser runtime is bounded on every input by the number of
available bit cells. -/
theorem decodeNatCompactRuntimeCosted_snd_le (bits : List Bool) :
    (decodeNatCompactRuntimeCosted bits).2 ≤ bits.length := by
  unfold decodeNatCompactRuntimeCosted
  generalize hw : decodeCompactWidthRuntimeCosted bits = widthResult
  rcases widthResult with ⟨widthOption, widthCost⟩
  cases widthOption with
  | none =>
      have h := decodeCompactWidthRuntimeCosted_snd_le bits
      rw [hw] at h
      exact h
  | some pair =>
      rcases pair with ⟨width, rest⟩
      have hwfst : (decodeCompactWidthRuntimeCosted bits).1 = some (width, rest) := by
        rw [hw]
      have hpartition := decodeCompactWidthRuntimeCosted_success_length hwfst
      have hpayload := decodePayloadRuntimeCosted_snd_le_length width rest
      rw [hw] at hpartition
      simp only at hpartition
      change widthCost + (decodePayloadRuntimeCosted width rest).2 ≤ bits.length
      omega

/-- A successful compact-natural parse performs exactly one recursive bit
inspection per consumed input cell. -/
theorem decodeNatCompactRuntimeCosted_success_length
    {bits : List Bool} {value : Nat} {tail : List Bool}
    (h : (decodeNatCompactRuntimeCosted bits).1 = some (value, tail)) :
    tail.length + (decodeNatCompactRuntimeCosted bits).2 = bits.length := by
  unfold decodeNatCompactRuntimeCosted at h ⊢
  generalize hw : decodeCompactWidthRuntimeCosted bits = widthResult at h ⊢
  rcases widthResult with ⟨widthOption, widthCost⟩
  cases widthOption with
  | none => simp at h
  | some pair =>
      rcases pair with ⟨width, rest⟩
      simp only at h ⊢
      generalize hp : decodePayloadRuntimeCosted width rest = payloadResult at h ⊢
      rcases payloadResult with ⟨payloadOption, payloadCost⟩
      cases payloadOption with
      | none => simp at h
      | some result =>
          rcases result with ⟨raw, suffix⟩
          by_cases hzero : raw = 0
          · simp [hzero] at h
          · simp only [hzero, if_false] at h
            have hwfst : (decodeCompactWidthRuntimeCosted bits).1 = some (width, rest) := by
              rw [hw]
            have hpfirst : (decodePayloadRuntimeCosted width rest).1 = some (raw, suffix) := by
              rw [hp]
            have hwidth := decodeCompactWidthRuntimeCosted_success_length hwfst
            have hpay := decodePayloadRuntimeCosted_success_length hpfirst
            rw [hw] at hwidth
            rw [hp] at hpay
            simp only at hwidth hpay
            cases h
            simp only
            omega

/-- Recursive decoder for exactly `count` compact natural fields. Its runtime
is the sum of the actual bit inspections performed by the field parsers. -/
def decodeWordsCompactRuntimeCosted :
    Nat → List Bool → Option (List Nat × List Bool) × Nat
  | 0, bits => (some ([], bits), 0)
  | count + 1, bits =>
      let first := decodeNatCompactRuntimeCosted bits
      match first.1 with
      | none => (none, first.2)
      | some (n, rest) =>
          let tailResult := decodeWordsCompactRuntimeCosted count rest
          let out := match tailResult.1 with
            | none => none
            | some (ns, tail) => some (n :: ns, tail)
          (out, first.2 + tailResult.2)

/-- Recursive word parsing erases to the accepted compact-word parser. -/
@[simp] theorem decodeWordsCompactRuntimeCosted_fst
    (count : Nat) (bits : List Bool) :
    (decodeWordsCompactRuntimeCosted count bits).1 = decodeWordsCompact count bits := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih =>
      simp only [decodeWordsCompactRuntimeCosted, decodeWordsCompact]
      generalize hf : decodeNatCompactRuntimeCosted bits = first
      rcases first with ⟨firstResult, firstCost⟩
      have hfirst := decodeNatCompactRuntimeCosted_fst bits
      rw [hf] at hfirst
      change firstResult = decodeNatCompact bits at hfirst
      rw [← hfirst]
      cases firstResult with
      | none => rfl
      | some pair =>
          rcases pair with ⟨n, rest⟩
          simp only
          generalize ht : decodeWordsCompactRuntimeCosted count rest = tailResult
          rcases tailResult with ⟨tailOption, tailCost⟩
          have ih' := ih rest
          rw [ht] at ih'
          change tailOption = decodeWordsCompact count rest at ih'
          rw [← ih']

/-- Word-list parsing performs no more bit inspections than there are input
cells, even on malformed and truncated inputs. -/
theorem decodeWordsCompactRuntimeCosted_snd_le
    (count : Nat) (bits : List Bool) :
    (decodeWordsCompactRuntimeCosted count bits).2 ≤ bits.length := by
  induction count generalizing bits with
  | zero => exact Nat.zero_le _
  | succ count ih =>
      unfold decodeWordsCompactRuntimeCosted
      generalize hf : decodeNatCompactRuntimeCosted bits = first
      rcases first with ⟨firstResult, firstCost⟩
      cases firstResult with
      | none =>
          have hfirst := decodeNatCompactRuntimeCosted_snd_le bits
          rw [hf] at hfirst
          exact hfirst
      | some pair =>
          rcases pair with ⟨n, rest⟩
          have hfirstResult :
              (decodeNatCompactRuntimeCosted bits).1 = some (n, rest) := by
            rw [hf]
          have hpartition := decodeNatCompactRuntimeCosted_success_length hfirstResult
          have htail := ih rest
          rw [hf] at hpartition
          simp only at hpartition
          change firstCost + (decodeWordsCompactRuntimeCosted count rest).2 ≤ bits.length
          omega

/-- A successful word-list parse inspects exactly the consumed prefix and never
the arbitrary trailing suffix. -/
theorem decodeWordsCompactRuntimeCosted_success_length
    {count : Nat} {bits : List Bool} {words : List Nat} {tail : List Bool}
    (h : (decodeWordsCompactRuntimeCosted count bits).1 = some (words, tail)) :
    tail.length + (decodeWordsCompactRuntimeCosted count bits).2 = bits.length := by
  induction count generalizing bits words tail with
  | zero =>
      simp only [decodeWordsCompactRuntimeCosted] at h ⊢
      cases h
      omega
  | succ count ih =>
      unfold decodeWordsCompactRuntimeCosted at h ⊢
      generalize hf : decodeNatCompactRuntimeCosted bits = first at h ⊢
      rcases first with ⟨firstResult, firstCost⟩
      cases firstResult with
      | none => simp at h
      | some pair =>
          rcases pair with ⟨n, rest⟩
          simp only at h ⊢
          generalize ht : decodeWordsCompactRuntimeCosted count rest = tailResult at h ⊢
          rcases tailResult with ⟨tailOption, tailCost⟩
          cases tailOption with
          | none => simp at h
          | some pair =>
              rcases pair with ⟨ns, suffix⟩
              simp only at h
              have hfirstResult :
                  (decodeNatCompactRuntimeCosted bits).1 = some (n, rest) := by
                rw [hf]
              have htailResult :
                  (decodeWordsCompactRuntimeCosted count rest).1 = some (ns, suffix) := by
                rw [ht]
              have hfirstLen := decodeNatCompactRuntimeCosted_success_length hfirstResult
              have htailLen := ih htailResult
              rw [hf] at hfirstLen
              rw [ht] at htailLen
              simp only at hfirstLen htailLen
              cases h
              simp only
              omega

/-- Primitive work counters for the recursive compact binary parser. Bit
inspections and word-format operations are deliberately separate units. -/
structure BinaryParserWork where
  bitInspections : Nat
  wordOperations : Nat
  deriving DecidableEq, Repr

/-- Every compact self-delimiting natural field contains at least its delimiter. -/
theorem compactNatFieldBits_pos (n : Nat) : 0 < compactNatFieldBits n := by
  unfold compactNatFieldBits
  omega

end OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
