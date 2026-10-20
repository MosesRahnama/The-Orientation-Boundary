import Mathlib.Computability.Halting
import OperatorKO7.Meta.BoundaryObserver.BoundaryPole
import OperatorKO7.Meta.BoundaryObserver.DemandDetector

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.RiceBoundary

open ProtocolResolution BoundarySingularity PairResolution MergedPair

/-- The bounded record stores evaluations on inputs through the chosen budget. -/
def boundedRecord (b : ℕ) (c : Nat.Partrec.Code) : Fin (b + 1) → Option ℕ :=
  fun n => Nat.Partrec.Code.evaln b c n.val

/-- The characteristic Boolean test of halting on input zero uses classical decidability. -/
noncomputable def haltingTest (c : Nat.Partrec.Code) : Bool := by
  classical
  exact decide ((c.eval 0).Dom)

/-- The padded input code reconstructs its input through a pair whose first component is the budget. -/
def paddedInput (b : ℕ) : Nat.Partrec.Code :=
  Nat.Partrec.Code.comp Nat.Partrec.Code.right
    (Nat.Partrec.Code.pair (Nat.Partrec.Code.const b) Nat.Partrec.Code.id)

/-- The padded code computes the original code after reconstructing its input. -/
def paddedCode (b : ℕ) (c : Nat.Partrec.Code) : Nat.Partrec.Code :=
  Nat.Partrec.Code.comp c (paddedInput b)

/-- Padded input reconstruction leaves the unbounded semantics unchanged. -/
theorem paddedInput_eval (b n : ℕ) :
    Nat.Partrec.Code.eval (paddedInput b) n = Part.some n := by
  change (Nat.Partrec.Code.eval
    (Nat.Partrec.Code.pair (Nat.Partrec.Code.const b) Nat.Partrec.Code.id) n >>=
      Nat.Partrec.Code.eval Nat.Partrec.Code.right) = Part.some n
  have hp : Nat.Partrec.Code.eval
      (Nat.Partrec.Code.pair (Nat.Partrec.Code.const b) Nat.Partrec.Code.id) n =
      Part.some (Nat.pair b n) := by
    simp [Nat.Partrec.Code.eval, Seq.seq]
  rw [hp]
  simp [Nat.Partrec.Code.eval, Nat.unpair_pair]

/-- The bounded evaluator cannot observe the padded input reconstruction. -/
theorem paddedInput_evaln_none (b n : ℕ) :
    Nat.Partrec.Code.evaln b (paddedInput b) n = none := by
  cases b with
  | zero => simp [paddedInput, Nat.Partrec.Code.evaln]
  | succ k =>
    cases hpair : Nat.Partrec.Code.evaln (k + 1)
        (Nat.Partrec.Code.pair (Nat.Partrec.Code.const (k + 1))
          Nat.Partrec.Code.id) n with
    | none =>
      simp [paddedInput, Nat.Partrec.Code.evaln.eq_7, hpair]
    | some w =>
      have hwsem : w ∈ Nat.Partrec.Code.eval
          (Nat.Partrec.Code.pair (Nat.Partrec.Code.const (k + 1))
            Nat.Partrec.Code.id) n := Nat.Partrec.Code.evaln_sound (by
              simpa only [Option.mem_def] using hpair)
      have hp : Nat.Partrec.Code.eval
          (Nat.Partrec.Code.pair (Nat.Partrec.Code.const (k + 1))
            Nat.Partrec.Code.id) n = Part.some (Nat.pair (k + 1) n) := by
        simp [Nat.Partrec.Code.eval, Seq.seq]
      rw [hp] at hwsem
      have hwval : w = Nat.pair (k + 1) n := by simpa using hwsem
      have hbig : k + 1 ≤ w := by
        rw [hwval]
        exact Nat.left_le_pair _ _
      have hright : Nat.Partrec.Code.evaln (k + 1)
          Nat.Partrec.Code.right w = none := by
        cases hout : Nat.Partrec.Code.evaln (k + 1) Nat.Partrec.Code.right w with
        | none => rfl
        | some v =>
          have hsmall : w < k + 1 := Nat.Partrec.Code.evaln_bound (by
            simpa only [Option.mem_def] using hout)
          exact (not_lt_of_ge hbig hsmall).elim
      simp [paddedInput, Nat.Partrec.Code.evaln.eq_7, hpair, hright]

/-- The padding does not change the partial function computed by a code. -/
theorem paddedCode_eval (b : ℕ) (c : Nat.Partrec.Code) :
    (paddedCode b c).eval = c.eval := by
  funext n
  change (Nat.Partrec.Code.eval (paddedInput b) n >>=
    Nat.Partrec.Code.eval c) = c.eval n
  rw [paddedInput_eval]
  simp

/-- Padded codes have no successful bounded evaluations at the padded budget. -/
theorem paddedCode_evaln_none (b : ℕ) (c : Nat.Partrec.Code) (n : ℕ) :
    Nat.Partrec.Code.evaln b (paddedCode b c) n = none := by
  cases b with
  | zero => simp [paddedCode, Nat.Partrec.Code.evaln]
  | succ k =>
    simp only [paddedCode, Nat.Partrec.Code.evaln.eq_7]
    simp [paddedInput_evaln_none]

/-- An extensional Boolean test is computable exactly when it is constant. -/
theorem rice_computable_iff_constant
    (P : Nat.Partrec.Code → Bool)
    (hExt : ∀ c c', c.eval = c'.eval → P c = P c') :
    ComputablePred (fun c => P c = true) ↔
      (∀ c, P c = true) ∨ (∀ c, P c = false) := by
  let C : Set Nat.Partrec.Code := {c | P c = true}
  have hC : ∀ cf cg, cf.eval = cg.eval → (cf ∈ C ↔ cg ∈ C) := by
    intro cf cg h
    change P cf = true ↔ P cg = true
    rw [hExt cf cg h]
  have hr := ComputablePred.rice₂ C hC
  constructor
  · intro hc
    have hc' : ComputablePred (fun c => c ∈ C) := hc
    rcases hr.mp hc' with hempty | huniv
    · right
      intro c
      have hf : P c ≠ true := by
        intro hp
        have hm : c ∈ C := hp
        rw [hempty] at hm
        exact Set.notMem_empty c hm
      cases h : P c with
      | false => rfl
      | true => exact (hf h).elim
    · left
      intro c
      have hm : c ∈ C := by rw [huniv]; trivial
      exact hm
  · intro h
    apply hr.mpr
    rcases h with ht | hf
    · right
      ext c
      simp [C, ht c]
    · left
      ext c
      simp [C, hf c]

/-- Every nonconstant extensional test has opposite labels on codes sharing a complete bounded record. -/
theorem bounded_record_merged_pair
    (P : Nat.Partrec.Code → Bool)
    (hExt : ∀ c c', c.eval = c'.eval → P c = P c')
    (hNon : ¬ ((∀ c, P c = true) ∨ (∀ c, P c = false)))
    (b : ℕ) :
    ∃ cPos cNeg : Nat.Partrec.Code,
      P cPos = true ∧ P cNeg = false ∧
        boundedRecord b cPos = boundedRecord b cNeg := by
  have hPos : ∃ c : Nat.Partrec.Code, P c = true := by
    by_contra h
    apply hNon
    right
    intro c
    cases hc : P c with
    | false => rfl
    | true => exact (h ⟨c, hc⟩).elim
  have hNeg : ∃ c : Nat.Partrec.Code, P c = false := by
    by_contra h
    apply hNon
    left
    intro c
    cases hc : P c with
    | true => rfl
    | false => exact (h ⟨c, hc⟩).elim
  obtain ⟨a, ha⟩ := hPos
  obtain ⟨z, hz⟩ := hNeg
  refine ⟨paddedCode b a, paddedCode b z, ?_, ?_, ?_⟩
  · exact (hExt (paddedCode b a) a (paddedCode_eval b a)).trans ha
  · exact (hExt (paddedCode b z) z (paddedCode_eval b z)).trans hz
  · funext i
    simp only [boundedRecord, paddedCode_evaln_none]

/-- Every reading determined by a bounded record has zero discrimination at its opposite-label pair. -/
theorem bounded_record_pole
    (P : Nat.Partrec.Code → Bool)
    (hExt : ∀ c c', c.eval = c'.eval → P c = P c')
    (hNon : ¬ ((∀ c, P c = true) ∨ (∀ c, P c = false)))
    (b : ℕ) :
    ∃ cPos cNeg : Nat.Partrec.Code,
      P cPos = true ∧ P cNeg = false ∧
      boundedRecord b cPos = boundedRecord b cNeg ∧
      ∀ (Y : Type) [Fintype Y] (K : BoundaryPole.Reading Nat.Partrec.Code Y),
        BoundaryPole.RecordDetermined (boundedRecord b) K →
          BoundaryPole.readingDiscrimination K cPos cNeg = 0 := by
  obtain ⟨cPos, cNeg, hPos, hNeg, heq⟩ :=
    bounded_record_merged_pair P hExt hNon b
  have hne : cPos ≠ cNeg := by
    intro h
    have hs := congrArg P h
    rw [hPos, hNeg] at hs
    cases hs
  refine ⟨cPos, cNeg, hPos, hNeg, heq, ?_⟩
  intro Y _ K hdet
  exact BoundaryPole.recordPoleGoal Nat.Partrec.Code
    (Fin (b + 1) → Option ℕ) Y (boundedRecord b) K cPos cNeg
    hdet ⟨hne, heq⟩

/-- Record-determined adaptive protocols at any merged bounded-record pair have zero information at every horizon and at the limit. -/
theorem bounded_record_protocol_pole
    (b : ℕ) (cPos cNeg : Nat.Partrec.Code)
    (hne : cPos ≠ cNeg)
    (heq : boundedRecord b cPos = boundedRecord b cNeg)
    {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y)
    (K : List (A × Y) → A → BoundaryPole.Reading Nat.Partrec.Code Y)
    (hdet : ∀ h a, BoundaryPole.RecordDetermined (boundedRecord b) (K h a))
    (hobs : ∀ h a v, p.observation h a v =
      K h a (BoundaryPole.pairState cPos cNeg v)) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧
      informationLimit p = 0 := by
  exact BoundaryPole.recordProtocolPoleGoal Nat.Partrec.Code
    (Fin (b + 1) → Option ℕ) A Y (boundedRecord b) cPos cNeg p K
    ⟨hne, heq⟩ hdet hobs

/-- Every total computable operation on codes has an extensional fixed point. -/
theorem rice_code_fixed_point
    (n : Nat.Partrec.Code → Nat.Partrec.Code) (hn : Computable n) :
    ∃ c : Nat.Partrec.Code, (n c).eval = c.eval :=
  Nat.Partrec.Code.fixed_point hn

/-- No computable code transformation implements a fixed-point-free change of an extensional Boolean label. -/
theorem no_fixed_point_free_boolean_code_map
    (P : Nat.Partrec.Code → Bool)
    (hExt : ∀ c c', c.eval = c'.eval → P c = P c')
    (n : Nat.Partrec.Code → Nat.Partrec.Code) (hn : Computable n)
    (j : Bool → Bool) (hj : ∀ v, j v ≠ v) :
    ¬ ∀ c, P (n c) = j (P c) := by
  intro h
  obtain ⟨c, hfix⟩ := rice_code_fixed_point n hn
  have heq := hExt (n c) c hfix
  rw [h c] at heq
  exact (hj (P c)) heq

/-- No computable code transformation negates an extensional Boolean test everywhere. -/
theorem no_negating_code_map
    (P : Nat.Partrec.Code → Bool)
    (hExt : ∀ c c', c.eval = c'.eval → P c = P c')
    (n : Nat.Partrec.Code → Nat.Partrec.Code) (hn : Computable n) :
    ¬ ∀ c, P (n c) = !P c := by
  intro hNeg
  obtain ⟨c, hfix⟩ := rice_code_fixed_point n hn
  have hsame := hExt (n c) c hfix
  rw [hNeg c] at hsame
  cases hc : P c <;> simp [hc] at hsame

/-- Halting on input zero is the union of the bounded halting observations. -/
theorem halting_union_of_bounded (c : Nat.Partrec.Code) :
    (c.eval 0).Dom ↔
      ∃ b : ℕ, Nat.Partrec.Code.evaln b c 0 ≠ none := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨b, hb⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    refine ⟨b, ?_⟩
    intro hnone
    simp [hnone] at hb
  · rintro ⟨b, hb⟩
    cases hval : Nat.Partrec.Code.evaln b c 0 with
    | none => exact (hb hval).elim
    | some v =>
      apply Part.dom_iff_mem.mpr
      refine ⟨v, Nat.Partrec.Code.evaln_sound (k := b) ?_⟩
      simpa only [Option.mem_def] using hval

/-- The zero-input halting set is semidecidable, and its complement is not. -/
theorem halting_semidecidable_complement_not :
    REPred (fun c : Nat.Partrec.Code => (c.eval 0).Dom) ∧
      ¬ REPred (fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom) :=
  ⟨ComputablePred.halting_problem_re 0,
    ComputablePred.halting_problem_not_re 0⟩

/-- Post's criterion equates computability with semidecidability on both sides of a predicate. -/
theorem post_computable_iff_semidecidable_and_complement
    (R : Nat.Partrec.Code → Prop) :
    ComputablePred R ↔ REPred R ∧ REPred (fun c => ¬ R c) := by
  exact ComputablePred.computable_iff_re_compl_re'

/-- The halting Boolean test is extensional and nonconstant, hence noncomputable by Rice's theorem. -/
theorem halting_test_not_computable :
    ¬ ComputablePred (fun c : Nat.Partrec.Code => haltingTest c = true) := by
  have hExt : ∀ c c' : Nat.Partrec.Code,
      c.eval = c'.eval → haltingTest c = haltingTest c' := by
    intro c c' h
    simp [haltingTest, h]
  have hSome : haltingTest Nat.Partrec.Code.zero = true := by
    classical
    unfold haltingTest
    apply decide_eq_true
    change (Part.some (0 : ℕ)).Dom
    trivial
  have hNone : ∃ c : Nat.Partrec.Code, haltingTest c = false := by
    have hp : Nat.Partrec (fun _ : ℕ => (Part.none : Part ℕ)) :=
      Nat.Partrec.none
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hp
    refine ⟨c, ?_⟩
    simp [haltingTest, hc]
  intro hComp
  have hc := (rice_computable_iff_constant haltingTest hExt).mp hComp
  rcases hc with hallTrue | hallFalse
  · obtain ⟨c, hfalse⟩ := hNone
    have h := hallTrue c
    rw [hfalse] at h
    cases h
  · have h := hallFalse Nat.Partrec.Code.zero
    rw [hSome] at h
    cases h

/-- Extensional Boolean tests are computable precisely when one Boolean value holds on every code. -/
theorem extensional_computable_iff_const
    (P : Nat.Partrec.Code → Bool)
    (hExt : ∀ c c', c.eval = c'.eval → P c = P c') :
    ComputablePred (fun c => P c = true) ↔
      ∃ v : Bool, ∀ c, P c = v := by
  constructor
  · intro h
    rcases (rice_computable_iff_constant P hExt).mp h with hTrue | hFalse
    · exact ⟨true, hTrue⟩
    · exact ⟨false, hFalse⟩
  · rintro ⟨v, hv⟩
    cases v with
    | false => exact (rice_computable_iff_constant P hExt).mpr (Or.inr hv)
    | true => exact (rice_computable_iff_constant P hExt).mpr (Or.inl hv)

/-- Every computable code map has an extensional fixed point and cannot uniformly apply a fixed-point-free Boolean relabeling. -/
theorem no_fixed_point_free_code_map
    (n : Nat.Partrec.Code → Nat.Partrec.Code) (hn : Computable n) :
    (∃ e : Nat.Partrec.Code, (n e).eval = e.eval) ∧
      ∀ (P : Nat.Partrec.Code → Bool),
        (∀ c c', c.eval = c'.eval → P c = P c') →
          ∀ (j : Bool → Bool),
            (∀ v, j v ≠ v) →
              ¬ ∀ c, P (n c) = j (P c) := by
  constructor
  · exact rice_code_fixed_point n hn
  · intro P hExt j hj
    exact no_fixed_point_free_boolean_code_map P hExt n hn j hj

/-- The zero-input halting set is the union of decidable bounded-record tests, is semidecidable only on the positive side, and satisfies Post's criterion. -/
theorem halting_one_sided :
    ({c : Nat.Partrec.Code | (c.eval 0).Dom} =
      ⋃ b : ℕ, {c : Nat.Partrec.Code |
        boundedRecord b c ⟨0, Nat.zero_lt_succ b⟩ ≠ none}) ∧
    (∀ b : ℕ, Nonempty (DecidablePred
      (fun c : Nat.Partrec.Code =>
        boundedRecord b c ⟨0, Nat.zero_lt_succ b⟩ ≠ none))) ∧
    REPred (fun c : Nat.Partrec.Code => (c.eval 0).Dom) ∧
    ¬ REPred (fun c : Nat.Partrec.Code => ¬ (c.eval 0).Dom) ∧
    (∀ R : Nat.Partrec.Code → Prop,
      ComputablePred R ↔ REPred R ∧ REPred (fun c => ¬ R c)) := by
  refine ⟨?_, ?_, halting_semidecidable_complement_not.1,
    halting_semidecidable_complement_not.2, ?_⟩
  · ext c
    simpa [boundedRecord] using halting_union_of_bounded c
  · intro b
    exact ⟨by intro c; infer_instance⟩
  · intro R
    exact post_computable_iff_semidecidable_and_complement R

/--
Proves: two codes with equal bounded records at every budget compute the same partial function.
The union of the bounded records determines the semantics observer `c ↦ c.eval`.
Does not prove: the converse; `bounded_records_finer_than_eval` refutes it.
Trust: kernel-only, through Mathlib's `evaln_complete`, `evaln_bound` and `evaln_sound`.
-/
theorem bounded_records_union_determines_eval (c c' : Nat.Partrec.Code)
    (h : ∀ b, boundedRecord b c = boundedRecord b c') : c.eval = c'.eval := by
  have key : ∀ d d' : Nat.Partrec.Code, (∀ b, boundedRecord b d = boundedRecord b d') →
      ∀ n v, v ∈ d.eval n → v ∈ d'.eval n := by
    intro d d' hd n v hv
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    have hnk : n < k := Nat.Partrec.Code.evaln_bound hk
    have hrec : Nat.Partrec.Code.evaln k d n = Nat.Partrec.Code.evaln k d' n :=
      congrFun (hd k) ⟨n, Nat.lt_succ_of_lt hnk⟩
    have hk' : v ∈ Nat.Partrec.Code.evaln k d' n := by
      rw [← hrec]
      exact hk
    exact Nat.Partrec.Code.evaln_sound hk'
  funext n
  apply Part.ext
  intro v
  exact ⟨key c c' h n v, key c' c (fun b => (h b).symm) n v⟩

/--
Proves: the union of the bounded records is finer than the semantics observer, since it records
running times: the zero code and its padded copy at a budget `k` at which the zero code halts on
input zero compute the same partial function and have different bounded records at `k`.
Trust: kernel-only, through `paddedCode_eval`, `paddedCode_evaln_none` and Mathlib's
`evaln_complete`.
-/
theorem bounded_records_finer_than_eval :
    ∃ c c' : Nat.Partrec.Code, c.eval = c'.eval ∧
      ∃ b, boundedRecord b c ≠ boundedRecord b c' := by
  have hz : (0 : ℕ) ∈ Nat.Partrec.Code.eval Nat.Partrec.Code.zero 0 := by
    change (0 : ℕ) ∈ Part.some 0
    exact Part.mem_some 0
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hz
  refine ⟨Nat.Partrec.Code.zero, paddedCode k Nat.Partrec.Code.zero,
    (paddedCode_eval k Nat.Partrec.Code.zero).symm, k, ?_⟩
  intro h
  have h0 : Nat.Partrec.Code.evaln k Nat.Partrec.Code.zero 0 =
      Nat.Partrec.Code.evaln k (paddedCode k Nat.Partrec.Code.zero) 0 :=
    congrFun h ⟨0, Nat.succ_pos k⟩
  rw [paddedCode_evaln_none] at h0
  rw [h0] at hk
  simp at hk

end OperatorKO7.Meta.BoundaryObserver.RiceBoundary
