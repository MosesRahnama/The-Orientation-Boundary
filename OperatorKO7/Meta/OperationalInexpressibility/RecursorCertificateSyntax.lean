import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
import OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization
import OperatorKO7.Meta.ArtsGiesl_ProofLengthBySize
import OperatorKO7.Meta.OperationalInexpressibility.CertificateCodecCore

/-!
# Executable recursor certificate syntax

The certificate records a root-rule reference, an occurrence path, a projection
coordinate and the two dependency-pair ranks.  Serialization is independent of
the input term.  The checker receives the same source and right-hand side that
the claim concerns and recomputes the structural equalities and rank decrease.

The compact codec and the costed word decoders are in `CertificateCodecCore`.
The final section separates this concrete serialized certificate cost from the
older assembly-cost model in `ArtsGiesl_ProofLengthBySize`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax

open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.FaithfulRecursorRealization
open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.ArtsGieslProofLengthBySize

inductive RootRuleRef where
  | zero
  | succ
deriving DecidableEq, Repr

/-- Finite certificate consumed by the same-input checker. -/
structure ExtractionCertificate where
  rule : RootRuleRef
  activePath : List Nat
  projectionArg : Nat
  rankBefore : Nat
  rankAfter : Nat
deriving DecidableEq, Repr

/-- Version tag for the current certificate syntax. -/
def certificateVersion : Nat := 1

def ruleCode : RootRuleRef → Nat
  | .zero => 0
  | .succ => 1

def decodeRuleCode : Nat → Option RootRuleRef
  | 0 => some .zero
  | 1 => some .succ
  | _ => none

/-- Prefix-free at the certificate-field level: the path length delimits the
only variable-length field. -/
def serialize (c : ExtractionCertificate) : List Nat :=
  [certificateVersion, ruleCode c.rule, c.activePath.length] ++
    c.activePath ++ [c.projectionArg, c.rankBefore, c.rankAfter]

/-- Total decoder. Extra trailing fields, unknown versions, unknown rule codes
and truncated path/suffix fields are rejected. -/
def deserialize (xs : List Nat) : Option ExtractionCertificate :=
  match xs with
  | version :: rule :: pathLen :: rest =>
      if version ≠ certificateVersion then none
      else
        match decodeRuleCode rule with
        | none => none
        | some rr =>
            let path := rest.take pathLen
            let suffix := rest.drop pathLen
            if path.length ≠ pathLen then none
            else
              match suffix with
              | projectionArg :: rankBefore :: rankAfter :: [] =>
                  some { rule := rr
                         activePath := path
                         projectionArg := projectionArg
                         rankBefore := rankBefore
                         rankAfter := rankAfter }
              | _ => none
  | _ => none

/-- Encoding then decoding returns the original certificate. -/
theorem deserialize_serialize (c : ExtractionCertificate) :
    deserialize (serialize c) = some c := by
  cases c with
  | mk rule path projection before after =>
      cases rule <;>
        simp [serialize, deserialize, certificateVersion, ruleCode, decodeRuleCode]

/-- The serialized word count separates a fixed six-word envelope from the
occurrence path. -/
theorem serialize_length (c : ExtractionCertificate) :
    (serialize c).length = c.activePath.length + 6 := by
  simp [serialize]

/-- Structural meaning of a certificate before it is accepted by the checker. -/
def CertificateMeaning (source rhs : RecursorTerm) (c : ExtractionCertificate) : Prop :=
  match c.rule with
  | .zero =>
      ∃ b s, source = .recR b s .void ∧ rhs = b ∧ c.activePath = [] ∧
        c.projectionArg = 0 ∧ c.rankBefore = 0 ∧ c.rankAfter = 0
  | .succ =>
      ∃ b s n, source = .recR b s (.delta n) ∧
        rhs = .app s (.recR b s n) ∧ c.activePath = [1] ∧
        c.projectionArg = 2 ∧ c.rankBefore = dpRank source ∧
        c.rankAfter = dpRank (.recR b s n) ∧ c.rankBefore = c.rankAfter + 1

/-- Same-input Boolean checker. No claimed source, target or rank is trusted
from the certificate itself. -/
def check (source rhs : RecursorTerm) (c : ExtractionCertificate) : Bool :=
  match c.rule with
  | .zero =>
      match source with
      | .recR b _ .void =>
          decide (rhs = b ∧ c.activePath = [] ∧ c.projectionArg = 0 ∧
            c.rankBefore = 0 ∧ c.rankAfter = 0)
      | _ => false
  | .succ =>
      match source with
      | .recR b s (.delta n) =>
          decide (rhs = .app s (.recR b s n) ∧ c.activePath = [1] ∧
            c.projectionArg = 2 ∧ c.rankBefore = dpRank source ∧
            c.rankAfter = dpRank (.recR b s n) ∧ c.rankBefore = c.rankAfter + 1)
      | _ => false

/-- The Boolean checker and the declarative certificate meaning agree. -/
theorem check_eq_true_iff (source rhs : RecursorTerm) (c : ExtractionCertificate) :
    check source rhs c = true ↔ CertificateMeaning source rhs c := by
  cases c with
  | mk rule path projection before after =>
      cases rule <;> cases source <;>
        simp [check, CertificateMeaning]
      all_goals rename_i b s n
      all_goals cases n <;> simp

/-- Every accepted certificate proves an actual free-recursion root step. -/
theorem check_sound_rootStep
    {source rhs : RecursorTerm} {c : ExtractionCertificate}
    (h : check source rhs c = true) : FreeRecursorStep source rhs := by
  have hm := (check_eq_true_iff source rhs c).1 h
  unfold CertificateMeaning at hm
  cases hr : c.rule with
  | zero =>
      rw [hr] at hm
      rcases hm with ⟨b, s, hsource, hrhs, _⟩
      subst source
      subst rhs
      exact .zero b s
  | succ =>
      rw [hr] at hm
      rcases hm with ⟨b, s, n, rfl, rfl, _⟩
      exact .succ b s n

/-- A checked successor certificate also proves that the extractor returns the
actual recursive callee and that the transformed-call rank drops by one. -/
theorem check_sound_successor
    {b s n rhs : RecursorTerm} {c : ExtractionCertificate}
    (hrule : c.rule = .succ)
    (h : check (.recR b s (.delta n)) rhs c = true) :
    rhs = .app s (.recR b s n) ∧
      extractCall (.recR b s (.delta n)) rhs = some (.recR b s n) ∧
      FreeRecursorDPPair (.recR b s (.delta n)) (.recR b s n) ∧
      dpRank (.recR b s (.delta n)) = dpRank (.recR b s n) + 1 := by
  have hm := (check_eq_true_iff (.recR b s (.delta n)) rhs c).1 h
  unfold CertificateMeaning at hm
  rw [hrule] at hm
  rcases hm with ⟨b', s', n', hsrc, hrhs, hpath, hproj, hbefore, hafter, hrank⟩
  cases hsrc
  have hcallee : rhs = .app s (.recR b s n) := hrhs
  subst rhs
  exact ⟨rfl, by simp [extractCall], .succ b s n, freeRecursor_dp_rank_exact (.succ b s n)⟩

/-- Constructor for every zero-rule input. -/
def zeroCertificate (_b _s : RecursorTerm) : ExtractionCertificate where
  rule := .zero
  activePath := []
  projectionArg := 0
  rankBefore := 0
  rankAfter := 0

/-- Constructor for every successor-rule input. -/
def successorCertificate (b s n : RecursorTerm) : ExtractionCertificate where
  rule := .succ
  activePath := [1]
  projectionArg := 2
  rankBefore := dpRank (.recR b s (.delta n))
  rankAfter := dpRank (.recR b s n)

@[simp] theorem check_zeroCertificate (b s : RecursorTerm) :
    check (.recR b s .void) b (zeroCertificate b s) = true := by
  simp [check, zeroCertificate]

@[simp] theorem check_successorCertificate (b s n : RecursorTerm) :
    check (.recR b s (.delta n)) (.app s (.recR b s n))
      (successorCertificate b s n) = true := by
  simp [check, successorCertificate, dpRank, deltaPrefix]

/-- Executable certificate constructor for the two free-recursion root rules. -/
def buildCertificate (source rhs : RecursorTerm) : Option ExtractionCertificate :=
  match source with
  | .recR b s .void => if rhs = b then some (zeroCertificate b s) else none
  | .recR b s (.delta n) =>
      if rhs = .app s (.recR b s n) then some (successorCertificate b s n) else none
  | _ => none

/-- The constructor returns a certificate exactly on free-recursion root steps. -/
theorem buildCertificate_isSome_iff (source rhs : RecursorTerm) :
    (buildCertificate source rhs).isSome ↔ FreeRecursorStep source rhs := by
  constructor
  · intro h
    cases source <;> simp [buildCertificate] at h
    case recR b s n =>
      cases n <;> simp at h
      case void =>
        subst rhs
        exact .zero b s
      case delta n =>
        subst rhs
        exact .succ b s n
  · intro h
    cases h <;> simp [buildCertificate]

/-- Every constructed certificate is accepted by the same-input checker. -/
theorem buildCertificate_checked
    {source rhs : RecursorTerm} {c : ExtractionCertificate}
    (h : buildCertificate source rhs = some c) : check source rhs c = true := by
  cases source <;> simp [buildCertificate] at h
  case recR b s n =>
    cases n <;> simp at h
    case void =>
      rcases h with ⟨hrhs, hc⟩
      subst rhs
      subst c
      exact check_zeroCertificate b s
    case delta n =>
      rcases h with ⟨hrhs, hc⟩
      subst rhs
      subst c
      exact check_successorCertificate b s n

/-- Every actual free-recursion root step has a concrete checked certificate. -/
theorem rootStep_has_checked_certificate
    {source rhs : RecursorTerm} (h : FreeRecursorStep source rhs) :
    ∃ c, buildCertificate source rhs = some c ∧ check source rhs c = true := by
  have hs : (buildCertificate source rhs).isSome :=
    (buildCertificate_isSome_iff source rhs).2 h
  rcases Option.isSome_iff_exists.mp hs with ⟨c, hc⟩
  exact ⟨c, hc, buildCertificate_checked hc⟩

/-- The same constructor certifies every root step in every faithful
realization of the free recursor. -/
theorem faithful_rootStep_has_checked_certificate
    {X : Type*} (e : FaithfulRealization X)
    {source rhs : RecursorTerm} (h : FreeRecursorStep source rhs) :
    ∃ c, buildCertificate source rhs = some c ∧ check source rhs c = true ∧
      e.Root (e.encode source) (e.encode rhs) := by
  rcases rootStep_has_checked_certificate h with ⟨c, hc, hcheck⟩
  exact ⟨c, hc, hcheck, (e.freeRecursor_step_iff_realized_step source rhs).1 h⟩

/-- Serialized checking combines decoding and the same-input checker. -/
def checkSerialized (source rhs : RecursorTerm) (bytes : List Nat) : Bool :=
  match deserialize bytes with
  | none => false
  | some c => check source rhs c

@[simp] theorem checkSerialized_successorCertificate (b s n : RecursorTerm) :
    checkSerialized (.recR b s (.delta n)) (.app s (.recR b s n))
      (serialize (successorCertificate b s n)) = true := by
  simp [checkSerialized, deserialize_serialize]

/-- The same checked successor certificate survives every faithful realization:
the realized extractor returns the encoded active recursive call. -/
theorem faithful_successor_certificate
    {X : Type*} (e : FaithfulRealization X) (b s n : RecursorTerm) :
    check (.recR b s (.delta n)) (.app s (.recR b s n))
        (successorCertificate b s n) = true ∧
      e.extractor (e.point (.recR b s (.delta n)))
        (e.point (.app s (.recR b s n))) = some (e.point (.recR b s n)) := by
  constructor
  · exact check_successorCertificate b s n
  · rw [e.extractor_point]
    simp [extractCall]

/-- Unknown rule tags are rejected. -/
theorem malformed_rule_rejected :
    deserialize [certificateVersion, 9, 0, 0, 0, 0] = none := by decide

/-- A path length larger than the supplied path is rejected. -/
theorem out_of_range_path_rejected :
    deserialize [certificateVersion, 1, 4, 1, 2, 1, 0] = none := by decide

/-- Extra trailing words are rejected. -/
theorem trailing_words_rejected :
    deserialize [certificateVersion, 0, 0, 0, 0, 0, 99] = none := by decide

/-! ## Actual certificate size and check-cost accounting -/

/-- Number of syntax-tree nodes in a free recursor term. -/
def termNodes : RecursorTerm → Nat
  | .void => 1
  | .delta t => termNodes t + 1
  | .integrate t => termNodes t + 1
  | .merge a b => termNodes a + termNodes b + 1
  | .app a b => termNodes a + termNodes b + 1
  | .recR b s n => termNodes b + termNodes s + termNodes n + 1
  | .eqWit a b => termNodes a + termNodes b + 1

/-- Every free recursor term contains at least one syntax-tree node. -/
theorem termNodes_pos (t : RecursorTerm) : 0 < termNodes t := by
  induction t <;> simp [termNodes]

/-- Tree representation cost if source and right-hand side are duplicated in
the certificate rather than referenced. -/
def treeDuplicatingInputWords (source rhs : RecursorTerm) : Nat :=
  termNodes source + termNodes rhs


/-- Exact compact bit cost of the serialized certificate words, excluding the
separate word-count pref used by `serializeBits`. -/
def sharedCertificateBits (c : ExtractionCertificate) : Nat :=
  ((serialize c).map compactNatFieldBits).sum

/-- Input-dependent descent evidence is the exact compact cost of the two rank
fields, including their self-delimiting width prefixes. -/
def descentEvidenceBits (c : ExtractionCertificate) : Nat :=
  compactNatFieldBits c.rankBefore + compactNatFieldBits c.rankAfter

/-- Historical field-count proxy retained only to separate it from actual
algorithmic work below. It is not a checker-operation theorem. -/
def legacyFieldCheckerSteps (c : ExtractionCertificate) : Nat :=
  8 + c.activePath.length

/-- Historical wrapper retained for comparison only. -/
def legacyCheckSerializedWithBound
    (source rhs : RecursorTerm) (bytes : List Nat) : Bool × Nat :=
  match deserialize bytes with
  | none => (false, bytes.length)
  | some c => (check source rhs c, bytes.length + legacyFieldCheckerSteps c)

/-- The historical wrapper still returns the same Boolean answer. -/
theorem legacyCheckSerializedWithBound_fst
    (source rhs : RecursorTerm) (bytes : List Nat) :
    (legacyCheckSerializedWithBound source rhs bytes).1 = checkSerialized source rhs bytes := by
  unfold legacyCheckSerializedWithBound checkSerialized
  cases h : deserialize bytes <;> simp

/-- Zero-rule certificates contain six serialized natural-number words. -/
theorem zeroCertificate_serialized_word_count (b s : RecursorTerm) :
    (serialize (zeroCertificate b s)).length = 6 := by
  simp [serialize_length, zeroCertificate]

/-- Successor certificates contain seven serialized natural-number words. -/
theorem successorCertificate_serialized_word_count (b s n : RecursorTerm) :
    (serialize (successorCertificate b s n)).length = 7 := by
  simp [serialize_length, successorCertificate]

/-! ## Recursive operation accounting -/

/-- Recursive term equality paired with the number of constructor/equality
nodes inspected by this evaluator. -/
def termEqCost : RecursorTerm → RecursorTerm → Bool × Nat
  | .void, .void => (true, 1)
  | .delta a, .delta b =>
      let r := termEqCost a b
      (r.1, r.2 + 1)
  | .integrate a, .integrate b =>
      let r := termEqCost a b
      (r.1, r.2 + 1)
  | .merge a₁ a₂, .merge b₁ b₂ =>
      let r₁ := termEqCost a₁ b₁
      let r₂ := termEqCost a₂ b₂
      (r₁.1 && r₂.1, r₁.2 + r₂.2 + 1)
  | .app a₁ a₂, .app b₁ b₂ =>
      let r₁ := termEqCost a₁ b₁
      let r₂ := termEqCost a₂ b₂
      (r₁.1 && r₂.1, r₁.2 + r₂.2 + 1)
  | .recR a₁ a₂ a₃, .recR b₁ b₂ b₃ =>
      let r₁ := termEqCost a₁ b₁
      let r₂ := termEqCost a₂ b₂
      let r₃ := termEqCost a₃ b₃
      (r₁.1 && r₂.1 && r₃.1, r₁.2 + r₂.2 + r₃.2 + 1)
  | .eqWit a₁ a₂, .eqWit b₁ b₂ =>
      let r₁ := termEqCost a₁ b₁
      let r₂ := termEqCost a₂ b₂
      (r₁.1 && r₂.1, r₁.2 + r₂.2 + 1)
  | _, _ => (false, 1)

@[simp] theorem termEqCost_fst (a b : RecursorTerm) :
    (termEqCost a b).1 = decide (a = b) := by
  induction a generalizing b <;> cases b <;>
    simp_all [termEqCost, Bool.and_assoc]

/-- This evaluator never inspects more syntax nodes than the two input trees
contain together. -/
theorem termEqCost_snd_le (a b : RecursorTerm) :
    (termEqCost a b).2 ≤ termNodes a + termNodes b := by
  induction a generalizing b with
  | void => cases b <;> simp [termEqCost, termNodes]
  | delta a ih =>
      have ha := termNodes_pos a
      cases b <;> simp [termEqCost, termNodes] <;> try omega
      rename_i b
      have h := ih b
      omega
  | integrate a ih =>
      have ha := termNodes_pos a
      cases b <;> simp [termEqCost, termNodes] <;> try omega
      rename_i b
      have h := ih b
      omega
  | merge a1 a2 ih1 ih2 =>
      have ha := termNodes_pos a1
      cases b <;> simp [termEqCost, termNodes] <;> try omega
      rename_i b1 b2
      have h1 := ih1 b1
      have h2 := ih2 b2
      omega
  | app a1 a2 ih1 ih2 =>
      have ha := termNodes_pos a1
      cases b <;> simp [termEqCost, termNodes] <;> try omega
      rename_i b1 b2
      have h1 := ih1 b1
      have h2 := ih2 b2
      omega
  | recR a1 a2 a3 ih1 ih2 ih3 =>
      have ha := termNodes_pos a1
      cases b <;> simp [termEqCost, termNodes] <;> try omega
      rename_i b1 b2 b3
      have h1 := ih1 b1
      have h2 := ih2 b2
      have h3 := ih3 b3
      omega
  | eqWit a1 a2 ih1 ih2 =>
      have ha := termNodes_pos a1
      cases b <;> simp [termEqCost, termNodes] <;> try omega
      rename_i b1 b2
      have h1 := ih1 b1
      have h2 := ih2 b2
      omega

/-- Recursive equality for occurrence paths. -/
def pathEqCost : List Nat → List Nat → Bool × Nat
  | [], [] => (true, 1)
  | a :: as, b :: bs =>
      let r := pathEqCost as bs
      (decide (a = b) && r.1, r.2 + 1)
  | _, _ => (false, 1)

@[simp] theorem pathEqCost_fst (a b : List Nat) :
    (pathEqCost a b).1 = decide (a = b) := by
  induction a generalizing b with
  | nil => cases b <;> simp [pathEqCost]
  | cons x xs ih =>
      cases b with
      | nil => simp [pathEqCost]
      | cons y ys => simp [pathEqCost, ih]

/-- Path equality work is bounded by both list lengths plus the terminating
constructor comparison. -/
theorem pathEqCost_snd_le (a b : List Nat) :
    (pathEqCost a b).2 ≤ a.length + b.length + 1 := by
  induction a generalizing b with
  | nil => cases b <;> simp [pathEqCost]
  | cons x xs ih =>
      cases b with
      | nil => simp [pathEqCost]
      | cons y ys =>
          simp only [pathEqCost, List.length_cons]
          have h := ih ys
          omega

/-- Recursive delta-pref rank traversal with explicit operation count. -/
def deltaPrefixCosted : RecursorTerm → Nat × Nat
  | .delta n =>
      let r := deltaPrefixCosted n
      (r.1 + 1, r.2 + 1)
  | _ => (0, 1)

@[simp] theorem deltaPrefixCosted_fst (t : RecursorTerm) :
    (deltaPrefixCosted t).1 = deltaPrefix t := by
  induction t <;> simp_all [deltaPrefixCosted, deltaPrefix]

/-- Rank traversal is bounded by the traversed term tree size. -/
theorem deltaPrefixCosted_snd_le (t : RecursorTerm) :
    (deltaPrefixCosted t).2 ≤ termNodes t := by
  induction t with
  | delta t ih =>
      simp only [deltaPrefixCosted, termNodes]
      omega
  | void => simp [deltaPrefixCosted, termNodes]
  | integrate t ih => simp [deltaPrefixCosted, termNodes]
  | merge a b ih₁ ih₂ => simp [deltaPrefixCosted, termNodes]
  | app a b ih₁ ih₂ => simp [deltaPrefixCosted, termNodes]
  | recR b s n ih₁ ih₂ ih₃ => simp [deltaPrefixCosted, termNodes]
  | eqWit a b ih₁ ih₂ => simp [deltaPrefixCosted, termNodes]

/-- Dependency-pair rank paired with its explicit traversal work. -/
def dpRankCosted : RecursorTerm → Nat × Nat
  | .recR _ _ n =>
      let r := deltaPrefixCosted n
      (r.1, r.2 + 1)
  | _ => (0, 1)

@[simp] theorem dpRankCosted_fst (t : RecursorTerm) :
    (dpRankCosted t).1 = dpRank t := by
  cases t <;> simp [dpRankCosted, dpRank]

/-- Rank work is bounded by the whole source tree. -/
theorem dpRankCosted_snd_le (t : RecursorTerm) :
    (dpRankCosted t).2 ≤ termNodes t := by
  cases t with
  | recR b s n =>
      simp only [dpRankCosted, termNodes]
      have h := deltaPrefixCosted_snd_le n
      omega
  | void => simp [dpRankCosted, termNodes]
  | delta t => simp [dpRankCosted, termNodes]
  | integrate t => simp [dpRankCosted, termNodes]
  | merge a b => simp [dpRankCosted, termNodes]
  | app a b => simp [dpRankCosted, termNodes]
  | eqWit a b => simp [dpRankCosted, termNodes]

/-- Same-input certificate checker with an operation count derived from the
explicit recursive equality and rank evaluators above. -/
def checkCosted (source rhs : RecursorTerm) (c : ExtractionCertificate) : Bool × Nat :=
  match c.rule with
  | .zero =>
      match source with
      | .recR b _ .void =>
          let erhs := termEqCost rhs b
          let epath := pathEqCost c.activePath []
          (erhs.1 && epath.1 && decide (c.projectionArg = 0) &&
              decide (c.rankBefore = 0) && decide (c.rankAfter = 0),
            erhs.2 + epath.2 + 5)
      | _ => (false, 2)
  | .succ =>
      match source with
      | .recR b s (.delta n) =>
          let callee := .recR b s n
          let erhs := termEqCost rhs (.app s callee)
          let epath := pathEqCost c.activePath [1]
          let rbefore := dpRankCosted source
          let rafter := dpRankCosted callee
          (erhs.1 && epath.1 && decide (c.projectionArg = 2) &&
              decide (c.rankBefore = rbefore.1) &&
              decide (c.rankAfter = rafter.1) &&
              decide (c.rankBefore = c.rankAfter + 1),
            erhs.2 + epath.2 + rbefore.2 + rafter.2 + 6)
      | _ => (false, 2)

/-- The costed checker returns exactly the accepted checker Boolean. -/
@[simp] theorem checkCosted_fst (source rhs : RecursorTerm) (c : ExtractionCertificate) :
    (checkCosted source rhs c).1 = check source rhs c := by
  cases c with
  | mk rule path projection before after =>
      cases rule <;> cases source <;>
        simp [checkCosted, check, termEqCost_fst, pathEqCost_fst]
      all_goals rename_i b s n
      all_goals cases n <;> simp [Bool.and_assoc]

/-- Uniform upper bound on the explicit checker work for every input, accepted
or rejected. -/
def checkerOperationBudget (source rhs : RecursorTerm) (c : ExtractionCertificate) : Nat :=
  4 * termNodes source + termNodes rhs + 2 * c.activePath.length + 12

/-- The recursive checker work is bounded by source/RHS tree size and path size
on every input, including rejected certificates. -/
theorem checkCosted_snd_le_budget
    (source rhs : RecursorTerm) (c : ExtractionCertificate) :
    (checkCosted source rhs c).2 ≤ checkerOperationBudget source rhs c := by
  cases c with
  | mk rule path projection before after =>
      cases rule with
      | zero =>
          cases source with
          | recR b s n =>
              cases n with
              | void =>
                  have he := termEqCost_snd_le rhs b
                  have hp := pathEqCost_snd_le path []
                  have hp' : (pathEqCost path []).2 ≤ path.length + 1 := by
                    simpa using hp
                  have hbpos := termNodes_pos b
                  have hspos := termNodes_pos s
                  simp only [checkCosted, checkerOperationBudget, termNodes] at ⊢
                  omega
              | delta n => simp [checkCosted, checkerOperationBudget, termNodes]
              | integrate n => simp [checkCosted, checkerOperationBudget, termNodes]
              | merge a b => simp [checkCosted, checkerOperationBudget, termNodes]
              | app a b => simp [checkCosted, checkerOperationBudget, termNodes]
              | recR a b d => simp [checkCosted, checkerOperationBudget, termNodes]
              | eqWit a b => simp [checkCosted, checkerOperationBudget, termNodes]
          | void => simp [checkCosted, checkerOperationBudget, termNodes]
          | delta t => simp [checkCosted, checkerOperationBudget, termNodes]
          | integrate t => simp [checkCosted, checkerOperationBudget, termNodes]
          | merge a b => simp [checkCosted, checkerOperationBudget, termNodes]
          | app a b => simp [checkCosted, checkerOperationBudget, termNodes]
          | eqWit a b => simp [checkCosted, checkerOperationBudget, termNodes]
      | succ =>
          cases source with
          | recR b s n =>
              cases n with
              | delta n =>
                  have he := termEqCost_snd_le rhs (.app s (.recR b s n))
                  have hp := pathEqCost_snd_le path [1]
                  have hp' : (pathEqCost path [1]).2 ≤ path.length + 2 := by
                    simpa using hp
                  have hb := dpRankCosted_snd_le (.recR b s (.delta n))
                  have ha := dpRankCosted_snd_le (.recR b s n)
                  simp only [termNodes] at he hb ha
                  simp only [checkCosted, checkerOperationBudget, termNodes] at ⊢
                  omega
              | void => simp [checkCosted, checkerOperationBudget, termNodes]
              | integrate n => simp [checkCosted, checkerOperationBudget, termNodes]
              | merge a b => simp [checkCosted, checkerOperationBudget, termNodes]
              | app a b => simp [checkCosted, checkerOperationBudget, termNodes]
              | recR a b d => simp [checkCosted, checkerOperationBudget, termNodes]
              | eqWit a b => simp [checkCosted, checkerOperationBudget, termNodes]
          | void => simp [checkCosted, checkerOperationBudget, termNodes]
          | delta t => simp [checkCosted, checkerOperationBudget, termNodes]
          | integrate t => simp [checkCosted, checkerOperationBudget, termNodes]
          | merge a b => simp [checkCosted, checkerOperationBudget, termNodes]
          | app a b => simp [checkCosted, checkerOperationBudget, termNodes]
          | eqWit a b => simp [checkCosted, checkerOperationBudget, termNodes]


/-- Recursive parser for the certificate word format. The work coordinate counts
header inspections, path-pref traversal, rule decoding and suffix inspection. -/
def deserializeCosted (xs : List Nat) : Option ExtractionCertificate × Nat :=
  match xs with
  | version :: rule :: pathLen :: rest =>
      if version ≠ certificateVersion then (none, 4)
      else
        match decodeRuleCode rule with
        | none => (none, 5)
        | some rr =>
            let split := splitPrefixCosted pathLen rest
            match split.1 with
            | none => (none, split.2 + 5)
            | some (path, suffix) =>
                match suffix with
                | projectionArg :: rankBefore :: rankAfter :: [] =>
                    (some { rule := rr
                            activePath := path
                            projectionArg := projectionArg
                            rankBefore := rankBefore
                            rankAfter := rankAfter }, split.2 + 9)
                | _ => (none, split.2 + suffix.length + 6)
  | _ => (none, xs.length + 1)

/-- The recursive parser returns exactly the accepted word decoder result. -/
theorem deserializeCosted_fst (xs : List Nat) :
    (deserializeCosted xs).1 = deserialize xs := by
  cases xs with
  | nil => rfl
  | cons version xs =>
      cases xs with
      | nil => rfl
      | cons rule xs =>
          cases xs with
          | nil => rfl
          | cons pathLen rest =>
              simp only [deserializeCosted, deserialize]
              by_cases hv : version ≠ certificateVersion
              · simp [hv]
              · simp only [hv, if_false]
                cases hr : decodeRuleCode rule with
                | none => rfl
                | some rr =>
                    by_cases hlen : pathLen ≤ rest.length
                    · have hs := splitPrefixCosted_success pathLen rest hlen
                      rw [hs]
                      have htake : (rest.take pathLen).length = pathLen := by
                        simp [List.length_take, hlen]
                      generalize hdrop : rest.drop pathLen = suffix
                      cases suffix with
                      | nil => simp [htake]
                      | cons a suffix =>
                          cases suffix with
                          | nil => simp [htake]
                          | cons b suffix =>
                              cases suffix with
                              | nil => simp [htake]
                              | cons c suffix =>
                                  cases suffix with
                                  | nil => simp [htake]
                                  | cons d ds => simp [htake]
                    · have hlt : rest.length < pathLen := Nat.lt_of_not_ge hlen
                      have hs := splitPrefixCosted_none pathLen rest hlt
                      rw [hs]
                      have htake : (rest.take pathLen).length ≠ pathLen := by
                        rw [List.length_take, Nat.min_eq_right (Nat.le_of_lt hlt)]
                        omega
                      simp [hlen]

/-- Word-parser work is bounded on every input, including malformed and
truncated certificates. -/
theorem deserializeCosted_snd_le (xs : List Nat) :
    (deserializeCosted xs).2 ≤ 2 * xs.length + 10 := by
  cases xs with
  | nil => simp [deserializeCosted]
  | cons a xs =>
      cases xs with
      | nil => simp [deserializeCosted]
      | cons b xs =>
          cases xs with
          | nil => simp [deserializeCosted]
          | cons n rest =>
              simp only [deserializeCosted]
              by_cases hv : a ≠ certificateVersion
              · simp [hv]
              · simp only [hv, if_false]
                cases hr : decodeRuleCode b with
                | none => simp
                | some rr =>
                    cases hs : (splitPrefixCosted n rest).1 with
                    | none =>
                        have hcost := splitPrefixCosted_snd_le_length n rest
                        simp
                        omega
                    | some pr =>
                        rcases pr with ⟨pref, suffix⟩
                        have hp := (splitPrefixCosted_eq_some_iff n rest pref suffix).1 hs
                        have hsuf : suffix.length ≤ rest.length := by
                          rw [hp.2.2, List.length_drop]
                          omega
                        have hcost := splitPrefixCosted_snd_le_length n rest
                        cases suffix with
                        | nil => simp; omega
                        | cons x suffix =>
                            cases suffix with
                            | nil => simp; omega
                            | cons y suffix =>
                                cases suffix with
                                | nil => simp; omega
                                | cons z suffix =>
                                    cases suffix with
                                    | nil => simp; omega
                                    | cons w ws =>
                                        have hws : ws.length + 4 ≤ rest.length := by
                                          simpa using hsuf
                                        simp
                                        omega

/-- Fully costed serialized checker. Parsing and structural checking are counted
separately and then added. -/
def checkSerializedWithBound
    (source rhs : RecursorTerm) (bytes : List Nat) : Bool × Nat :=
  let parsed := deserializeCosted bytes
  match parsed.1 with
  | none => (false, parsed.2)
  | some c =>
      let checked := checkCosted source rhs c
      (checked.1, parsed.2 + checked.2)

/-- The recursive costed evaluator has exactly the same Boolean semantics as the
accepted serialized checker. -/
theorem checkSerializedWithBound_fst
    (source rhs : RecursorTerm) (bytes : List Nat) :
    (checkSerializedWithBound source rhs bytes).1 = checkSerialized source rhs bytes := by
  unfold checkSerializedWithBound checkSerialized
  generalize hdc : deserializeCosted bytes = dc
  rcases dc with ⟨parsed, parseCost⟩
  have hf := deserializeCosted_fst bytes
  rw [hdc] at hf
  change parsed = deserialize bytes at hf
  rw [← hf]
  cases parsed with
  | none => rfl
  | some c =>
      simp only
      exact checkCosted_fst source rhs c

/-- Successful decoding exposes the exact parser-plus-checker operation count. -/
theorem checkSerializedWithBound_snd_of_decode
    (source rhs : RecursorTerm) (bytes : List Nat) (c : ExtractionCertificate)
    (h : deserialize bytes = some c) :
    (checkSerializedWithBound source rhs bytes).2 =
      (deserializeCosted bytes).2 + (checkCosted source rhs c).2 := by
  unfold checkSerializedWithBound
  generalize hdc : deserializeCosted bytes = dc
  rcases dc with ⟨parsed, parseCost⟩
  have hf := deserializeCosted_fst bytes
  rw [hdc, h] at hf
  change parsed = some c at hf
  subst parsed
  rfl

/-- Parser plus checker work has an explicit source/RHS/path budget after a
successful parse. -/
theorem checkSerializedWithBound_snd_le_of_decode
    (source rhs : RecursorTerm) (bytes : List Nat) (c : ExtractionCertificate)
    (h : deserialize bytes = some c) :
    (checkSerializedWithBound source rhs bytes).2 ≤
      (deserializeCosted bytes).2 + checkerOperationBudget source rhs c := by
  rw [checkSerializedWithBound_snd_of_decode source rhs bytes c h]
  exact Nat.add_le_add_left (checkCosted_snd_le_budget source rhs c) _

/-- Total word-operation budget for the serialized checker. Malformed input pays
only the parser budget; a successfully decoded certificate additionally pays its
structural checker budget. -/
def serializedOperationBudget
    (source rhs : RecursorTerm) (bytes : List Nat) : Nat :=
  2 * bytes.length + 10 +
    match deserialize bytes with
    | none => 0
    | some c => checkerOperationBudget source rhs c

/-- The combined parser/checker operation count is bounded for every serialized
input, including malformed, truncated and otherwise rejected inputs. -/
theorem checkSerializedWithBound_snd_le_budget
    (source rhs : RecursorTerm) (bytes : List Nat) :
    (checkSerializedWithBound source rhs bytes).2 ≤
      serializedOperationBudget source rhs bytes := by
  unfold checkSerializedWithBound serializedOperationBudget
  generalize hdc : deserializeCosted bytes = dc
  rcases dc with ⟨parsed, parseCost⟩
  have hf := deserializeCosted_fst bytes
  rw [hdc] at hf
  change parsed = deserialize bytes at hf
  have hp := deserializeCosted_snd_le bytes
  rw [hdc] at hp
  rw [← hf]
  cases parsed with
  | none => simp; omega
  | some c =>
      have hc := checkCosted_snd_le_budget source rhs c
      simp
      omega

/-- Tree duplication cost is exactly the sum of the two input tree sizes. -/
theorem treeDuplicatingInputWords_eq (source rhs : RecursorTerm) :
    treeDuplicatingInputWords source rhs = termNodes source + termNodes rhs := rfl


/-- Actual compact binary certificate format. The word count is itself a compact
field, followed by compact encodings of all natural-number certificate words. -/
def serializeBits (c : ExtractionCertificate) : List Bool :=
  encodeNatCompact (serialize c).length ++ encodeWordsCompact (serialize c)

/-- Prefix parser for the actual compact binary certificate. It preserves the
unconsumed suffix so records can be concatenated. -/
def deserializeBitsPrefix (bits : List Bool) : Option (ExtractionCertificate × List Bool) :=
  match decodeNatCompact bits with
  | none => none
  | some (wordCount, rest) =>
      match decodeWordsCompact wordCount rest with
      | none => none
      | some (words, tail) =>
          match deserialize words with
          | none => none
          | some c => some (c, tail)

/-- Bit-cell accounting for the actual compact prefix parser. On success it
counts exactly the consumed prefix; on rejection it uses the full input length as
an upper bound. This metric is separate from word-level checker operations. -/
def deserializeBitsPrefixCosted
    (bits : List Bool) : Option (ExtractionCertificate × List Bool) × Nat :=
  match deserializeBitsPrefix bits with
  | none => (none, bits.length)
  | some result => (some result, bits.length - result.2.length)

@[simp] theorem deserializeBitsPrefixCosted_fst (bits : List Bool) :
    (deserializeBitsPrefixCosted bits).1 = deserializeBitsPrefix bits := by
  unfold deserializeBitsPrefixCosted
  cases deserializeBitsPrefix bits <;> rfl

/-- The actual compact binary parser consumes at most the available number of
bit cells on every input, including rejected encodings. -/
theorem deserializeBitsPrefixCosted_snd_le (bits : List Bool) :
    (deserializeBitsPrefixCosted bits).2 ≤ bits.length := by
  unfold deserializeBitsPrefixCosted
  cases deserializeBitsPrefix bits with
  | none => rfl
  | some result => exact Nat.sub_le _ _


/-- Fully instrumented compact parser. The bitstream is consumed by the recursive
compact decoders and the resulting word list is interpreted by the existing
recursive word deserializer. No cost is reconstructed from the final suffix. -/
def deserializeBitsPrefixRuntimeWork
    (bits : List Bool) : Option (ExtractionCertificate × List Bool) × BinaryParserWork :=
  let countResult := decodeNatCompactRuntimeCosted bits
  match countResult.1 with
  | none => (none, ⟨countResult.2, 0⟩)
  | some (wordCount, rest) =>
      let wordsResult := decodeWordsCompactRuntimeCosted wordCount rest
      match wordsResult.1 with
      | none => (none, ⟨countResult.2 + wordsResult.2, 0⟩)
      | some (words, tail) =>
          let decoded := deserializeCosted words
          let out := match decoded.1 with
            | none => none
            | some c => some (c, tail)
          (out, ⟨countResult.2 + wordsResult.2, decoded.2⟩)

/-- The fully instrumented parser erases exactly to the accepted compact parser. -/
@[simp] theorem deserializeBitsPrefixRuntimeWork_fst (bits : List Bool) :
    (deserializeBitsPrefixRuntimeWork bits).1 = deserializeBitsPrefix bits := by
  unfold deserializeBitsPrefixRuntimeWork deserializeBitsPrefix
  generalize hc : decodeNatCompactRuntimeCosted bits = countResult
  rcases countResult with ⟨countOption, countCost⟩
  have hcount := decodeNatCompactRuntimeCosted_fst bits
  rw [hc] at hcount
  change countOption = decodeNatCompact bits at hcount
  rw [← hcount]
  cases countOption with
  | none => rfl
  | some pair =>
      rcases pair with ⟨wordCount, rest⟩
      simp only
      generalize hw : decodeWordsCompactRuntimeCosted wordCount rest = wordsResult
      rcases wordsResult with ⟨wordsOption, wordsBitCost⟩
      have hwords := decodeWordsCompactRuntimeCosted_fst wordCount rest
      rw [hw] at hwords
      change wordsOption = decodeWordsCompact wordCount rest at hwords
      rw [← hwords]
      cases wordsOption with
      | none => rfl
      | some pair =>
          rcases pair with ⟨words, tail⟩
          simp only
          rw [deserializeCosted_fst]

/-- Actual recursive bit parsing inspects no more bit cells than are present,
including malformed and truncated encodings. -/
theorem deserializeBitsPrefixRuntimeWork_bitInspections_le (bits : List Bool) :
    (deserializeBitsPrefixRuntimeWork bits).2.bitInspections ≤ bits.length := by
  unfold deserializeBitsPrefixRuntimeWork
  generalize hc : decodeNatCompactRuntimeCosted bits = countResult
  rcases countResult with ⟨countOption, countCost⟩
  cases countOption with
  | none =>
      have hcount := decodeNatCompactRuntimeCosted_snd_le bits
      rw [hc] at hcount
      exact hcount
  | some pair =>
      rcases pair with ⟨wordCount, rest⟩
      have hcountResult :
          (decodeNatCompactRuntimeCosted bits).1 = some (wordCount, rest) := by
        rw [hc]
      have hcountLen := decodeNatCompactRuntimeCosted_success_length hcountResult
      generalize hw : decodeWordsCompactRuntimeCosted wordCount rest = wordsResult
      rcases wordsResult with ⟨wordsOption, wordsBitCost⟩
      have hwords := decodeWordsCompactRuntimeCosted_snd_le wordCount rest
      rw [hc] at hcountLen
      rw [hw] at hwords
      simp only at hcountLen hwords
      cases wordsOption <;> simp [hw] <;> omega

/-- Word-deserializer work is bounded on every input by the recursive word
parser's proved primitive budget for the word list that was actually produced.
Inputs that never produce a complete word list incur zero word-format operations. -/
def binaryParserWordBudget (bits : List Bool) : Nat :=
  match decodeNatCompact bits with
  | none => 0
  | some (wordCount, rest) =>
      match decodeWordsCompact wordCount rest with
      | none => 0
      | some (words, _) => 2 * words.length + 10

/-- The fully instrumented parser satisfies its word-operation budget on every
input, independently of whether the word list is a valid certificate. -/
theorem deserializeBitsPrefixRuntimeWork_wordOperations_le (bits : List Bool) :
    (deserializeBitsPrefixRuntimeWork bits).2.wordOperations ≤ binaryParserWordBudget bits := by
  unfold deserializeBitsPrefixRuntimeWork binaryParserWordBudget
  generalize hc : decodeNatCompactRuntimeCosted bits = countResult
  rcases countResult with ⟨countOption, countCost⟩
  have hcount := decodeNatCompactRuntimeCosted_fst bits
  rw [hc] at hcount
  change countOption = decodeNatCompact bits at hcount
  rw [← hcount]
  cases countOption with
  | none => rfl
  | some pair =>
      rcases pair with ⟨wordCount, rest⟩
      simp only
      generalize hw : decodeWordsCompactRuntimeCosted wordCount rest = wordsResult
      rcases wordsResult with ⟨wordsOption, wordsBitCost⟩
      have hwords := decodeWordsCompactRuntimeCosted_fst wordCount rest
      rw [hw] at hwords
      change wordsOption = decodeWordsCompact wordCount rest at hwords
      rw [← hwords]
      cases wordsOption with
      | none => rfl
      | some pair =>
          rcases pair with ⟨words, tail⟩
          simp only
          exact deserializeCosted_snd_le words

/-- On every successful parse, the parser's recursive bit-inspection count is
exactly the consumed prefix length. This is an operational theorem about the
instrumented recursion, not a posthoc definition from the returned suffix. -/
theorem deserializeBitsPrefixRuntimeWork_success_length
    {bits : List Bool} {c : ExtractionCertificate} {tail : List Bool}
    (h : (deserializeBitsPrefixRuntimeWork bits).1 = some (c, tail)) :
    tail.length + (deserializeBitsPrefixRuntimeWork bits).2.bitInspections = bits.length := by
  unfold deserializeBitsPrefixRuntimeWork at h ⊢
  generalize hc : decodeNatCompactRuntimeCosted bits = countResult at h ⊢
  rcases countResult with ⟨countOption, countCost⟩
  cases countOption with
  | none => simp at h
  | some pair =>
      rcases pair with ⟨wordCount, rest⟩
      simp only at h ⊢
      generalize hw : decodeWordsCompactRuntimeCosted wordCount rest = wordsResult at h ⊢
      rcases wordsResult with ⟨wordsOption, wordsBitCost⟩
      cases wordsOption with
      | none => simp at h
      | some pair =>
          rcases pair with ⟨words, suffix⟩
          simp only at h ⊢
          generalize hd : deserializeCosted words = decoded at h ⊢
          rcases decoded with ⟨certOption, wordCost⟩
          cases certOption with
          | none => simp at h
          | some cert =>
              simp only at h
              have hcountResult :
                  (decodeNatCompactRuntimeCosted bits).1 = some (wordCount, rest) := by
                rw [hc]
              have hwordsResult :
                  (decodeWordsCompactRuntimeCosted wordCount rest).1 = some (words, suffix) := by
                rw [hw]
              have hcountLen := decodeNatCompactRuntimeCosted_success_length hcountResult
              have hwordsLen := decodeWordsCompactRuntimeCosted_success_length hwordsResult
              rw [hc] at hcountLen
              rw [hw] at hwordsLen
              simp only at hcountLen hwordsLen
              cases h
              omega

/-- Compact binary certificate pref parsing round-trips and preserves trailing bits. -/
theorem deserializeBitsPrefix_serializeBits_append
    (c : ExtractionCertificate) (tail : List Bool) :
    deserializeBitsPrefix (serializeBits c ++ tail) = some (c, tail) := by
  unfold deserializeBitsPrefix serializeBits
  rw [List.append_assoc, decodeNatCompact_encode_append]
  simp only
  rw [decodeWordsCompact_encode_append (serialize c) tail]
  simp [deserialize_serialize]

@[simp] theorem deserializeBitsPrefix_serializeBits (c : ExtractionCertificate) :
    deserializeBitsPrefix (serializeBits c) = some (c, []) := by
  simpa using deserializeBitsPrefix_serializeBits_append c []

/-- Exact bit cost of the actual compact binary certificate. -/
def serializedBinaryBits (c : ExtractionCertificate) : Nat :=
  (serializeBits c).length

/-- Canonical compact certificates are parsed with exact bit-inspection cost,
and an arbitrary following suffix is returned without being inspected. -/
theorem deserializeBitsPrefixRuntimeWork_serializeBits_append
    (c : ExtractionCertificate) (tail : List Bool) :
    (deserializeBitsPrefixRuntimeWork (serializeBits c ++ tail)).1 = some (c, tail) ∧
      (deserializeBitsPrefixRuntimeWork (serializeBits c ++ tail)).2.bitInspections =
        serializedBinaryBits c := by
  have hparse :
      (deserializeBitsPrefixRuntimeWork (serializeBits c ++ tail)).1 = some (c, tail) := by
    rw [deserializeBitsPrefixRuntimeWork_fst, deserializeBitsPrefix_serializeBits_append]
  refine ⟨hparse, ?_⟩
  have hlen := deserializeBitsPrefixRuntimeWork_success_length hparse
  simp only [List.length_append] at hlen
  unfold serializedBinaryBits
  omega

/-- Exact compact bit-length theorem. The first term is the self-delimiting
word-count field; `sharedCertificateBits` is the exact compact cost of the
certificate words themselves. -/
theorem serializedBinaryBits_eq
    (c : ExtractionCertificate) :
    serializedBinaryBits c =
      compactNatFieldBits (serialize c).length + sharedCertificateBits c := by
  simp [serializedBinaryBits, serializeBits, sharedCertificateBits]

/-- Binary checker uses the pref parser and the accepted same-input checker. -/
def checkSerializedBits (source rhs : RecursorTerm) (bits : List Bool) : Bool :=
  match deserializeBitsPrefix bits with
  | none => false
  | some (c, _) => check source rhs c

/-- The prefix checker applied to a serialized certificate depends only on that certificate;
trailing bits remain available to a surrounding stream parser. -/
theorem checkSerializedBits_serializeBits_append
    (source rhs : RecursorTerm) (c : ExtractionCertificate) (tail : List Bool) :
    checkSerializedBits source rhs (serializeBits c ++ tail) = check source rhs c := by
  unfold checkSerializedBits
  rw [deserializeBitsPrefix_serializeBits_append]

/-- The prefix checker agrees with the same-input checker on a complete canonical certificate. -/
@[simp] theorem checkSerializedBits_serializeBits
    (source rhs : RecursorTerm) (c : ExtractionCertificate) :
    checkSerializedBits source rhs (serializeBits c) = check source rhs c := by
  simpa using checkSerializedBits_serializeBits_append source rhs c []

/-- Strict binary checker for a complete message. It accepts only when the compact parser
consumes the entire input. -/
def checkSerializedBitsStrict
    (source rhs : RecursorTerm) (bits : List Bool) : Bool :=
  match deserializeBitsPrefix bits with
  | some (c, []) => check source rhs c
  | _ => false

/-- Separate runtime units for strict compact-certificate checking. Parsing
work retains its bit/word split; proof checking has its own operation count. -/
structure BinaryCheckWork where
  parser : BinaryParserWork
  checkerOperations : Nat
  deriving DecidableEq, Repr

/-- Strict compact checker with recursively generated parser work and the
existing recursive proof-checker work. The counters are produced by execution,
not reconstructed from the final Boolean result. -/
def checkSerializedBitsStrictRuntimeCosted
    (source rhs : RecursorTerm) (bits : List Bool) : Bool × BinaryCheckWork :=
  let parsed := deserializeBitsPrefixRuntimeWork bits
  match parsed.1 with
  | some (c, []) =>
      let checked := checkCosted source rhs c
      (checked.1, ⟨parsed.2, checked.2⟩)
  | _ => (false, ⟨parsed.2, 0⟩)

/-- The fully costed strict checker has exactly the accepted strict-checker
Boolean semantics. -/
@[simp] theorem checkSerializedBitsStrictRuntimeCosted_fst
    (source rhs : RecursorTerm) (bits : List Bool) :
    (checkSerializedBitsStrictRuntimeCosted source rhs bits).1 =
      checkSerializedBitsStrict source rhs bits := by
  unfold checkSerializedBitsStrictRuntimeCosted checkSerializedBitsStrict
  generalize hp : deserializeBitsPrefixRuntimeWork bits = parsed
  rcases parsed with ⟨parsedOption, parserWork⟩
  have hpfirst := deserializeBitsPrefixRuntimeWork_fst bits
  rw [hp] at hpfirst
  change parsedOption = deserializeBitsPrefix bits at hpfirst
  rw [← hpfirst]
  cases parsedOption with
  | none => rfl
  | some pair =>
      rcases pair with ⟨c, rest⟩
      cases rest with
      | nil => simp [checkCosted_fst]
      | cons b tail => rfl

/-- Strict checking preserves the parser's exact work record in every branch. -/
theorem checkSerializedBitsStrictRuntimeCosted_parser
    (source rhs : RecursorTerm) (bits : List Bool) :
    (checkSerializedBitsStrictRuntimeCosted source rhs bits).2.parser =
      (deserializeBitsPrefixRuntimeWork bits).2 := by
  unfold checkSerializedBitsStrictRuntimeCosted
  cases h : deserializeBitsPrefixRuntimeWork bits with
  | mk result work =>
      cases result with
      | none => rfl
      | some pair =>
          rcases pair with ⟨c, rest⟩
          cases rest <;> rfl

/-- Consequently, strict-check bit inspections have the same all-input bound as
the recursive parser. -/
theorem checkSerializedBitsStrictRuntimeCosted_bitInspections_le
    (source rhs : RecursorTerm) (bits : List Bool) :
    (checkSerializedBitsStrictRuntimeCosted source rhs bits).2.parser.bitInspections ≤
      bits.length := by
  rw [checkSerializedBitsStrictRuntimeCosted_parser]
  exact deserializeBitsPrefixRuntimeWork_bitInspections_le bits

/-- Input-relative proof-checker budget after strict parsing. Parser and checker
costs remain separate units rather than being added into a dimensionless total. -/
def strictBinaryCheckerOperationBudget
    (source rhs : RecursorTerm) (bits : List Bool) : Nat :=
  match deserializeBitsPrefix bits with
  | some (c, []) => checkerOperationBudget source rhs c
  | _ => 0

/-- The proof-checker component satisfies its primitive all-input budget. -/
theorem checkSerializedBitsStrictRuntimeCosted_checkerOperations_le
    (source rhs : RecursorTerm) (bits : List Bool) :
    (checkSerializedBitsStrictRuntimeCosted source rhs bits).2.checkerOperations ≤
      strictBinaryCheckerOperationBudget source rhs bits := by
  unfold checkSerializedBitsStrictRuntimeCosted strictBinaryCheckerOperationBudget
  generalize hp : deserializeBitsPrefixRuntimeWork bits = parsed
  rcases parsed with ⟨parsedOption, parserWork⟩
  have hpfirst := deserializeBitsPrefixRuntimeWork_fst bits
  rw [hp] at hpfirst
  change parsedOption = deserializeBitsPrefix bits at hpfirst
  rw [← hpfirst]
  cases parsedOption with
  | none => rfl
  | some pair =>
      rcases pair with ⟨c, rest⟩
      cases rest with
      | nil =>
          simp only
          exact checkCosted_snd_le_budget source rhs c
      | cons b tail => rfl

/-- On a canonical serialized certificate, the costed strict checker agrees with
the same-input checker. -/
@[simp] theorem checkSerializedBitsStrictRuntimeCosted_serializeBits
    (source rhs : RecursorTerm) (c : ExtractionCertificate) :
    (checkSerializedBitsStrictRuntimeCosted source rhs (serializeBits c)).1 =
      check source rhs c := by
  rw [checkSerializedBitsStrictRuntimeCosted_fst]
  unfold checkSerializedBitsStrict
  rw [deserializeBitsPrefix_serializeBits]

/-- On a canonical serialized certificate, the strict checker agrees with the same-input checker. -/
@[simp] theorem checkSerializedBitsStrict_serializeBits
    (source rhs : RecursorTerm) (c : ExtractionCertificate) :
    checkSerializedBitsStrict source rhs (serializeBits c) = check source rhs c := by
  unfold checkSerializedBitsStrict
  rw [deserializeBitsPrefix_serializeBits]

/-- The strict checker rejects every canonical certificate followed by at least one trailing bit. -/
theorem checkSerializedBitsStrict_rejects_trailing
    (source rhs : RecursorTerm) (c : ExtractionCertificate)
    (bit : Bool) (tail : List Bool) :
    checkSerializedBitsStrict source rhs (serializeBits c ++ bit :: tail) = false := by
  unfold checkSerializedBitsStrict
  rw [deserializeBitsPrefix_serializeBits_append]

/-- Every bitstream accepted by the strict binary checker certifies an actual
free-recursion root step on the same source and right-hand side. -/
theorem checkSerializedBitsStrict_sound_rootStep
    {source rhs : RecursorTerm} {bits : List Bool}
    (h : checkSerializedBitsStrict source rhs bits = true) :
    FreeRecursorStep source rhs := by
  unfold checkSerializedBitsStrict at h
  cases hp : deserializeBitsPrefix bits with
  | none => simp [hp] at h
  | some parsed =>
      rcases parsed with ⟨c, rest⟩
      cases rest with
      | nil =>
          simp only [hp] at h
          exact check_sound_rootStep h
      | cons bit tail => simp [hp] at h

/-- Every actual free-recursion root step has a canonical compact strict binary
certificate. -/
theorem rootStep_has_strict_binary_certificate
    {source rhs : RecursorTerm} (h : FreeRecursorStep source rhs) :
    ∃ c, buildCertificate source rhs = some c ∧
      checkSerializedBitsStrict source rhs (serializeBits c) = true := by
  rcases rootStep_has_checked_certificate h with ⟨c, hbuild, hcheck⟩
  refine ⟨c, hbuild, ?_⟩
  rw [checkSerializedBitsStrict_serializeBits]
  exact hcheck

/-- Strict compact binary certificate existence is equivalent to the actual
free-recursion root-step relation. -/
theorem exists_strict_binary_certificate_iff_rootStep
    (source rhs : RecursorTerm) :
    (∃ bits, checkSerializedBitsStrict source rhs bits = true) ↔
      FreeRecursorStep source rhs := by
  constructor
  · rintro ⟨bits, hbits⟩
    exact checkSerializedBitsStrict_sound_rootStep hbits
  · intro hstep
    rcases rootStep_has_strict_binary_certificate hstep with ⟨c, _, hcheck⟩
    exact ⟨serializeBits c, hcheck⟩

/-- Every serialized successor certificate is accepted by the prefix binary checker. -/
@[simp] theorem checkSerializedBits_successorCertificate (b s n : RecursorTerm) :
    checkSerializedBits (.recR b s (.delta n)) (.app s (.recR b s n))
      (serializeBits (successorCertificate b s n)) = true := by
  rw [checkSerializedBits_serializeBits]
  exact check_successorCertificate b s n

/-- Every serialized successor certificate is accepted as a complete strict message. -/
@[simp] theorem checkSerializedBitsStrict_successorCertificate (b s n : RecursorTerm) :
    checkSerializedBitsStrict (.recR b s (.delta n)) (.app s (.recR b s n))
      (serializeBits (successorCertificate b s n)) = true := by
  rw [checkSerializedBitsStrict_serializeBits]
  exact check_successorCertificate b s n

/-- Bit cost of all serialized fields except the two descent ranks. -/
def certificateEnvelopeBits (c : ExtractionCertificate) : Nat :=
  compactNatFieldBits certificateVersion + compactNatFieldBits (ruleCode c.rule) +
    compactNatFieldBits c.activePath.length +
    (c.activePath.map compactNatFieldBits).sum +
    compactNatFieldBits c.projectionArg


/-- Shared/indexed bit cost splits into structural envelope plus the two
input-dependent descent ranks. -/
theorem sharedCertificateBits_decomposition (c : ExtractionCertificate) :
    sharedCertificateBits c = certificateEnvelopeBits c + descentEvidenceBits c := by
  simp [sharedCertificateBits, serialize, certificateEnvelopeBits, descentEvidenceBits]
  omega

/-- The actual serialized word count depends only on the path length; rank values
change bit cost but not word count. -/
theorem actual_word_cost_decomposition (c : ExtractionCertificate) :
    (serialize c).length = 6 + c.activePath.length := by
  rw [serialize_length]
  omega

/-- The older recursor formula is retained as an assembly-cost theorem. -/
theorem old_assembly_model_formula (m K : Nat) :
    agProofLength linearBaseOrder (recursorShape m) + K = 4 * m + 2 + K :=
  confessionCertificateLength_recursor m K

/-- Concrete separation: the serialized successor certificate has seven words,
while the old assembly formula at `m=1,K=0` is six. Therefore the old formula
is not an encoding theorem for this certificate syntax. -/
theorem assembly_model_not_serialized_word_count :
    (serialize (successorCertificate .void .void .void)).length ≠ 4 * 1 + 2 + 0 := by
  decide

/-- Concrete shared/index cost includes the input-dependent rank field. -/
theorem successor_descent_evidence_nonzero :
    0 < descentEvidenceBits (successorCertificate .void .void .void) := by
  unfold descentEvidenceBits
  exact Nat.add_pos_left (compactNatFieldBits_pos _) _

end OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
