import OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax

/-!
# Accepted bitstrings of the strict certificate checker

`decodeNatCompact` accepts a payload whose width prefix announces more cells
than `(n + 1).bits` needs, provided the extra cells are `false`. This file proves
that this padding is the only freedom in the compact certificate format. For any
source and right-hand side, the strict checker accepts exactly the padded
encodings of the words of `buildCertificate`; every accepted bitstring decodes
to that certificate; and `serializeBits` is the unique shortest accepted
bitstring.
-/

namespace OperatorKO7.Meta.OperationalInexpressibility.CertificateAcceptedSet

open OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.Recursor.DPConfessionLicense

/-- Compact field for `n` whose width prefix announces `pad` payload cells
beyond `(n + 1).bits`; the extra cells are `false`. -/
def encodeNatPadded (n pad : Nat) : List Bool :=
  encodeCompactWidth (compactNatWidth n + pad) ++ ((n + 1).bits ++ List.replicate pad false)

/-- Padded fields for a word list, one padding per word. -/
def encodeWordsPadded : List Nat → List Nat → List Bool
  | [], _ => []
  | _ :: _, [] => []
  | n :: ns, p :: ps => encodeNatPadded n p ++ encodeWordsPadded ns ps

/-- Padded certificate format: the padded word-count field, then the padded
words. -/
def serializeBitsPadded (c : ExtractionCertificate) (pad : Nat) (pads : List Nat) :
    List Bool :=
  encodeNatPadded (serialize c).length pad ++ encodeWordsPadded (serialize c) pads

theorem encodeNatPadded_zero (n : Nat) : encodeNatPadded n 0 = encodeNatCompact n := by
  simp [encodeNatPadded, encodeNatCompact]

theorem encodeWordsPadded_replicate_zero (ws : List Nat) :
    encodeWordsPadded ws (List.replicate ws.length 0) = encodeWordsCompact ws := by
  induction ws with
  | nil => rfl
  | cons n ns ih =>
      simp only [List.length_cons, List.replicate_succ, encodeWordsPadded, encodeNatPadded_zero,
        ih, encodeWordsCompact]

theorem serializeBitsPadded_zero (c : ExtractionCertificate) :
    serializeBitsPadded c 0 (List.replicate (serialize c).length 0) = serializeBits c := by
  simp only [serializeBitsPadded, encodeNatPadded_zero, encodeWordsPadded_replicate_zero,
    serializeBits]

/-! ## Payload values -/

theorem bitsToNat_replicate_false (k : Nat) : bitsToNat (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, bitsToNat, ih, Nat.bit_val]

theorem bitsToNat_append_replicate_false (l : List Bool) (k : Nat) :
    bitsToNat (l ++ List.replicate k false) = bitsToNat l := by
  induction l with
  | nil => simp [bitsToNat, bitsToNat_replicate_false]
  | cons b bs ih => simp [bitsToNat, ih]

/-- Every payload is the binary digits of its value followed by `false` cells. -/
theorem bits_bitsToNat_append_replicate (p : List Bool) :
    (bitsToNat p).bits.length ≤ p.length ∧
      p = (bitsToNat p).bits ++ List.replicate (p.length - (bitsToNat p).bits.length) false := by
  induction p with
  | nil => simp [bitsToNat, Nat.zero_bits]
  | cons b bs ih =>
      obtain ⟨hle, heq⟩ := ih
      by_cases hz : bitsToNat bs = 0 ∧ b = false
      · obtain ⟨hv, rfl⟩ := hz
        have hzero : bitsToNat (false :: bs) = 0 := by simp [bitsToNat, hv, Nat.bit_val]
        have hbs : bs = List.replicate bs.length false := by
          rw [hv, Nat.zero_bits] at heq
          simpa using heq
        rw [hzero, Nat.zero_bits]
        refine ⟨Nat.zero_le _, ?_⟩
        simp only [List.nil_append, List.length_nil, Nat.sub_zero, List.length_cons,
          List.replicate_succ]
        exact congrArg (List.cons false) hbs
      · have hn : bitsToNat bs = 0 → b = true := by
          intro hv
          cases b with
          | false => exact absurd ⟨hv, rfl⟩ hz
          | true => rfl
        have hbits : (bitsToNat (b :: bs)).bits = b :: (bitsToNat bs).bits :=
          Nat.bits_append_bit (bitsToNat bs) b hn
        rw [hbits]
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        simp only [List.length_cons, Nat.add_sub_add_right, List.cons_append]
        exact congrArg (List.cons b) heq

/-! ## Accepted compact fields -/

theorem decodeCompactWidth_eq_some_iff {bits rest : List Bool} {w : Nat} :
    decodeCompactWidth bits = some (w, rest) ↔ bits = encodeCompactWidth w ++ rest := by
  constructor
  · intro h
    induction bits generalizing w with
    | nil => simp [decodeCompactWidth] at h
    | cons b bs ih =>
        cases b with
        | false =>
            simp only [decodeCompactWidth, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        | true =>
            simp only [decodeCompactWidth] at h
            cases hr : decodeCompactWidth bs with
            | none => simp [hr] at h
            | some pair =>
                rcases pair with ⟨m, tail⟩
                simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                simp only [ih hr, encodeCompactWidth, List.cons_append]
  · rintro rfl
    exact decodeCompactWidth_encode_append w rest

/-- A compact field decodes to `n` exactly when it is a padded encoding of `n`. -/
theorem decodeNatCompact_eq_some_iff {bits : List Bool} {n : Nat} {tail : List Bool} :
    decodeNatCompact bits = some (n, tail) ↔ ∃ pad, bits = encodeNatPadded n pad ++ tail := by
  constructor
  · intro h
    unfold decodeNatCompact at h
    cases hw : decodeCompactWidth bits with
    | none => simp [hw] at h
    | some pair =>
        rcases pair with ⟨width, rest⟩
        simp only [hw] at h
        by_cases h1 : (rest.take width).length ≠ width
        · rw [if_pos h1] at h
          cases h
        · rw [if_neg h1] at h
          by_cases h2 : bitsToNat (rest.take width) = 0
          · rw [if_pos h2] at h
            cases h
          · rw [if_neg h2] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hn, rfl⟩ := h
            have hlen : (rest.take width).length = width := not_not.mp h1
            have hval : bitsToNat (rest.take width) = n + 1 := by omega
            obtain ⟨hle, hpay⟩ := bits_bitsToNat_append_replicate (rest.take width)
            rw [hval, hlen] at hle hpay
            have hbits := decodeCompactWidth_eq_some_iff.1 hw
            refine ⟨width - compactNatWidth n, ?_⟩
            have hcw : compactNatWidth n = (n + 1).bits.length := rfl
            have hwidth : (n + 1).bits.length + (width - (n + 1).bits.length) = width := by
              omega
            rw [encodeNatPadded, hcw, hwidth, ← hpay, List.append_assoc, List.take_append_drop]
            exact hbits
  · rintro ⟨pad, rfl⟩
    have hX : ((n + 1).bits ++ List.replicate pad false).length = compactNatWidth n + pad := by
      simp [compactNatWidth]
    have hval : bitsToNat ((n + 1).bits ++ List.replicate pad false) = n + 1 := by
      rw [bitsToNat_append_replicate_false, bitsToNat_bits]
    unfold decodeNatCompact encodeNatPadded
    rw [List.append_assoc, decodeCompactWidth_encode_append]
    simp only
    rw [List.take_left' hX, List.drop_left' hX]
    simp [hX, hval]

/-- `count` compact fields decode to `ws` exactly when they are padded
encodings of `ws`, one padding per word. -/
theorem decodeWordsCompact_eq_some_iff (count : Nat) (bits : List Bool) (ws : List Nat)
    (tail : List Bool) :
    decodeWordsCompact count bits = some (ws, tail) ↔
      ws.length = count ∧ ∃ pads : List Nat, pads.length = count ∧
        bits = encodeWordsPadded ws pads ++ tail := by
  induction count generalizing bits ws with
  | zero =>
      constructor
      · intro h
        simp only [decodeWordsCompact, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, [], rfl, rfl⟩
      · rintro ⟨hlen, pads, -, rfl⟩
        obtain rfl := List.eq_nil_of_length_eq_zero hlen
        rfl
  | succ n ih =>
      constructor
      · intro h
        cases h1 : decodeNatCompact bits with
        | none => simp [decodeWordsCompact, h1] at h
        | some pair =>
            rcases pair with ⟨m, rest⟩
            cases h2 : decodeWordsCompact n rest with
            | none => simp [decodeWordsCompact, h1, h2] at h
            | some pair2 =>
                rcases pair2 with ⟨ms, tail'⟩
                simp only [decodeWordsCompact, h1, h2, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨pad, hpad⟩ := decodeNatCompact_eq_some_iff.1 h1
                obtain ⟨hlen, pads, hpads, hrest⟩ := (ih rest ms).1 h2
                refine ⟨by simp [hlen], pad :: pads, by simp [hpads], ?_⟩
                rw [hpad, hrest]
                simp [encodeWordsPadded, List.append_assoc]
      · rintro ⟨hlen, pads, hpads, rfl⟩
        cases ws with
        | nil => simp at hlen
        | cons m ms =>
            cases pads with
            | nil => simp at hpads
            | cons p ps =>
                simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen hpads
                have h1 : decodeNatCompact (encodeWordsPadded (m :: ms) (p :: ps) ++ tail) =
                    some (m, encodeWordsPadded ms ps ++ tail) :=
                  decodeNatCompact_eq_some_iff.2
                    ⟨p, by simp [encodeWordsPadded, List.append_assoc]⟩
                have h2 : decodeWordsCompact n (encodeWordsPadded ms ps ++ tail) =
                    some (ms, tail) :=
                  (ih _ ms).2 ⟨hlen, ps, hpads, rfl⟩
                simp only [decodeWordsCompact, h1, h2]

/-! ## Words and certificates -/

theorem ruleCode_of_decodeRuleCode {r : Nat} {rr : RootRuleRef}
    (h : decodeRuleCode r = some rr) : ruleCode rr = r := by
  unfold decodeRuleCode at h
  split at h
  · cases h
    rfl
  · cases h
    rfl
  · cases h

/-- The word decoder accepts only the serialization of its output. -/
theorem eq_serialize_of_deserialize {xs : List Nat} {c : ExtractionCertificate}
    (h : deserialize xs = some c) : xs = serialize c := by
  unfold deserialize at h
  split at h
  next version rule pathLen rest =>
    split at h
    next => cases h
    next hv =>
      split at h
      next => cases h
      next rr hr =>
        try simp only at h
        split at h
        next => cases h
        next hl =>
          split at h
          next a b d hd =>
            cases h
            have hv' : version = certificateVersion := not_not.mp hv
            have hl' : (rest.take pathLen).length = pathLen := not_not.mp hl
            have hrule := ruleCode_of_decodeRuleCode hr
            have hrest : rest = rest.take pathLen ++ [a, b, d] := by
              rw [← hd, List.take_append_drop]
            simp only [serialize, hrule, hl', hv']
            conv_lhs => rw [hrest]
            simp
          next => cases h
  next => cases h

theorem deserialize_eq_some_iff (xs : List Nat) (c : ExtractionCertificate) :
    deserialize xs = some c ↔ xs = serialize c :=
  ⟨eq_serialize_of_deserialize, fun h => h ▸ deserialize_serialize c⟩

/-- The same-input checker accepts exactly the constructed certificate. -/
theorem check_eq_true_iff_buildCertificate (source rhs : RecursorTerm)
    (c : ExtractionCertificate) :
    check source rhs c = true ↔ buildCertificate source rhs = some c := by
  refine ⟨fun h => ?_, buildCertificate_checked⟩
  have hm := (check_eq_true_iff source rhs c).1 h
  rcases c with ⟨rule, path, proj, before, after⟩
  cases rule with
  | zero =>
      obtain ⟨b, s, rfl, rfl, hp, hj, hb, ha⟩ := hm
      simp only at hp hj hb ha
      subst hp hj hb ha
      simp [buildCertificate, zeroCertificate]
  | succ =>
      obtain ⟨b, s, n, rfl, rfl, hp, hj, hb, ha, -⟩ := hm
      simp only at hp hj hb ha
      subst hp hj hb ha
      simp [buildCertificate, successorCertificate]

/-! ## The accepted set -/

theorem deserializeBitsPrefix_eq_some_nil_iff (bits : List Bool) (c : ExtractionCertificate) :
    deserializeBitsPrefix bits = some (c, []) ↔
      ∃ pad pads, pads.length = (serialize c).length ∧ bits = serializeBitsPadded c pad pads := by
  constructor
  · intro hp
    unfold deserializeBitsPrefix at hp
    cases h1 : decodeNatCompact bits with
    | none => simp [h1] at hp
    | some pair =>
        rcases pair with ⟨wc, rest⟩
        cases h2 : decodeWordsCompact wc rest with
        | none => simp [h1, h2] at hp
        | some pair2 =>
            rcases pair2 with ⟨words, tail⟩
            cases h3 : deserialize words with
            | none => simp [h1, h2, h3] at hp
            | some c' =>
                simp only [h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at hp
                obtain ⟨hc, ht⟩ := hp
                subst hc
                subst ht
                have hw := eq_serialize_of_deserialize h3
                subst hw
                obtain ⟨pad, hpad⟩ := decodeNatCompact_eq_some_iff.1 h1
                obtain ⟨hlen, pads, hpads, hrest⟩ :=
                  (decodeWordsCompact_eq_some_iff wc rest (serialize c') []).1 h2
                refine ⟨pad, pads, by rw [hpads, hlen], ?_⟩
                rw [hpad, hrest, List.append_nil, ← hlen]
                rfl
  · rintro ⟨pad, pads, hpads, rfl⟩
    have h1 : decodeNatCompact (serializeBitsPadded c pad pads) =
        some ((serialize c).length, encodeWordsPadded (serialize c) pads) :=
      decodeNatCompact_eq_some_iff.2 ⟨pad, rfl⟩
    have h2 : decodeWordsCompact (serialize c).length (encodeWordsPadded (serialize c) pads) =
        some (serialize c, []) :=
      (decodeWordsCompact_eq_some_iff _ _ _ _).2 ⟨rfl, pads, hpads, (List.append_nil _).symm⟩
    unfold deserializeBitsPrefix
    rw [h1]
    simp only [h2, deserialize_serialize]

/-- P4.2, accepted set: the strict checker accepts exactly the padded encodings
of the words of the constructed certificate. -/
theorem checkSerializedBitsStrict_eq_true_iff (source rhs : RecursorTerm) (bits : List Bool) :
    checkSerializedBitsStrict source rhs bits = true ↔
      ∃ c, buildCertificate source rhs = some c ∧
        ∃ pad pads, pads.length = (serialize c).length ∧
          bits = serializeBitsPadded c pad pads := by
  constructor
  · intro h
    unfold checkSerializedBitsStrict at h
    cases hp : deserializeBitsPrefix bits with
    | none => simp [hp] at h
    | some parsed =>
        rcases parsed with ⟨c, rest⟩
        cases rest with
        | cons b t => simp [hp] at h
        | nil =>
            simp only [hp] at h
            exact ⟨c, (check_eq_true_iff_buildCertificate source rhs c).1 h,
              (deserializeBitsPrefix_eq_some_nil_iff bits c).1 hp⟩
  · rintro ⟨c, hbuild, hpad⟩
    unfold checkSerializedBitsStrict
    rw [(deserializeBitsPrefix_eq_some_nil_iff bits c).2 hpad]
    exact buildCertificate_checked hbuild

/-- Every strictly accepted bitstring decodes to the constructed certificate. -/
theorem deserializeBitsPrefix_of_checkSerializedBitsStrict {source rhs : RecursorTerm}
    {c : ExtractionCertificate} (hbuild : buildCertificate source rhs = some c)
    {bits : List Bool} (h : checkSerializedBitsStrict source rhs bits = true) :
    deserializeBitsPrefix bits = some (c, []) := by
  obtain ⟨c', hbuild', hpad⟩ := (checkSerializedBitsStrict_eq_true_iff source rhs bits).1 h
  rw [hbuild] at hbuild'
  cases hbuild'
  exact (deserializeBitsPrefix_eq_some_nil_iff bits c).2 hpad

/-! ## Lengths and canonicality -/

theorem encodeNatPadded_length (n pad : Nat) :
    (encodeNatPadded n pad).length = compactNatFieldBits n + 2 * pad := by
  have h := encodeNatCompact_length n
  simp only [encodeNatCompact, List.length_append, encodeCompactWidth_length] at h
  simp only [encodeNatPadded, List.length_append, encodeCompactWidth_length,
    List.length_replicate]
  omega

theorem encodeWordsPadded_length (ws pads : List Nat) (h : pads.length = ws.length) :
    (encodeWordsPadded ws pads).length = (encodeWordsCompact ws).length + 2 * pads.sum := by
  induction ws generalizing pads with
  | nil =>
      cases pads with
      | nil => rfl
      | cons p ps => simp at h
  | cons n ns ih =>
      cases pads with
      | nil => simp at h
      | cons p ps =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp only [encodeWordsPadded, encodeWordsCompact, List.length_append,
            encodeNatPadded_length, encodeNatCompact_length, ih ps h, List.sum_cons]
          omega

theorem serializeBitsPadded_length (c : ExtractionCertificate) (pad : Nat) (pads : List Nat)
    (hpads : pads.length = (serialize c).length) :
    (serializeBitsPadded c pad pads).length = serializedBinaryBits c + 2 * (pad + pads.sum) := by
  have h := encodeWordsPadded_length (serialize c) pads hpads
  simp only [serializeBitsPadded, serializedBinaryBits, serializeBits, List.length_append,
    encodeNatPadded_length, encodeNatCompact_length, h]
  omega

theorem eq_replicate_zero_of_sum_eq_zero :
    ∀ l : List Nat, l.sum = 0 → l = List.replicate l.length 0
  | [], _ => rfl
  | a :: as, h => by
      simp only [List.sum_cons] at h
      have ha : a = 0 := by omega
      have ih := eq_replicate_zero_of_sum_eq_zero as (by omega)
      subst ha
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons 0) ih

/-- P4.2, canonicality: every strictly accepted bitstring for the constructed
certificate `c` has at least `serializedBinaryBits c` cells, and
`serializeBits c` is the only accepted bitstring of that length. -/
theorem checkSerializedBitsStrict_length_canonical {source rhs : RecursorTerm}
    {c : ExtractionCertificate} (hbuild : buildCertificate source rhs = some c)
    {bits : List Bool} (h : checkSerializedBitsStrict source rhs bits = true) :
    serializedBinaryBits c ≤ bits.length ∧
      (bits.length = serializedBinaryBits c ↔ bits = serializeBits c) := by
  obtain ⟨c', hbuild', pad, pads, hpads, rfl⟩ :=
    (checkSerializedBitsStrict_eq_true_iff source rhs bits).1 h
  rw [hbuild] at hbuild'
  cases hbuild'
  rw [serializeBitsPadded_length c pad pads hpads]
  refine ⟨Nat.le_add_right _ _, ⟨fun hlen => ?_, fun heq => ?_⟩⟩
  · have hp : pad = 0 := by omega
    have hps : pads.sum = 0 := by omega
    rw [hp, eq_replicate_zero_of_sum_eq_zero pads hps, hpads]
    exact serializeBitsPadded_zero c
  · rw [← serializeBitsPadded_length c pad pads hpads, heq]
    rfl

/-- Control: the successor certificate with one padding cell on its word-count
field is strictly accepted and is two cells longer than `serializeBits`. -/
theorem padded_successorCertificate_accepted (b s n : RecursorTerm) :
    checkSerializedBitsStrict (.recR b s (.delta n)) (.app s (.recR b s n))
        (serializeBitsPadded (successorCertificate b s n) 1
          (List.replicate (serialize (successorCertificate b s n)).length 0)) = true ∧
      (serializeBitsPadded (successorCertificate b s n) 1
          (List.replicate (serialize (successorCertificate b s n)).length 0)).length =
        serializedBinaryBits (successorCertificate b s n) + 2 := by
  constructor
  · rw [checkSerializedBitsStrict_eq_true_iff]
    exact ⟨successorCertificate b s n, by simp [buildCertificate], 1, _, by simp, rfl⟩
  · rw [serializeBitsPadded_length _ _ _ (by simp)]
    simp

end OperatorKO7.Meta.OperationalInexpressibility.CertificateAcceptedSet
