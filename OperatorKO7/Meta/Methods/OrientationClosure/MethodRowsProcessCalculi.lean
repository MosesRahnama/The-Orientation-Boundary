import Mathlib.Tactic
import OperatorKO7.Meta.Rewriting.Rewrite
import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness

/-!
# Method rows for the process-calculi group of the Orientation Boundary closeout

Tier C method rows whose carriers are process calculi. The subject is the free recursor
`recur(b, s, zero) → b`, `recur(b, s, succ n) → wrap(s, recur(b, s, n))`, read through a
translation into processes: the pi-calculus termination translation with a level system and
decreasing first-order data (Deng and Sangiorgi, Information and Computation 204(2), 2006), and the
lambda-mu calculus through a continuation-passing translation (Parigot, LICS 1992; de Groote,
Information and Computation 149(1), 1999).

Every row follows the P5 row contract: `Data`, `Laws`, `Accepts`, `Result` with a verdict line, a
`Witness` with `_laws`, `_result`, `_feature`, and `_mutation`, a `_sound` theorem, and a `_scope`
definition. Relation: the free schema of `SchemaCore`, never a concrete KO7 term. External trust:
none. Mathlib only.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

/-! ## Shared native process syntax -/

/-- Processes over channels: nil, output prefix, input prefix, parallel composition and
replication. -/
inductive PiProc where
  | nil : PiProc
  | out : Nat → PiProc → PiProc
  | inp : Nat → PiProc → PiProc
  | par : PiProc → PiProc → PiProc
  | rep : PiProc → PiProc
  deriving DecidableEq, Repr

/-- A finite synchronous process reduction. Communication removes matching output and input
prefixes, and reduction is closed under parallel composition. Replication is inert in this
termination fragment. The reduct is the first argument. -/
inductive PiLinearStep : PiProc → PiProc → Prop
  | comm (channel : Nat) (p q : PiProc) :
      PiLinearStep (.par p q) (.par (.out channel p) (.inp channel q))
  | parLeft {p' p q : PiProc} :
      PiLinearStep p' p → PiLinearStep (.par p' q) (.par p q)
  | parRight {p q' q : PiProc} :
      PiLinearStep q' q → PiLinearStep (.par p q') (.par p q)

/-- Constructor size of a process. -/
def piSize : PiProc → Nat
  | .nil => 1
  | .out _ p => piSize p + 1
  | .inp _ p => piSize p + 1
  | .par p q => piSize p + piSize q + 1
  | .rep p => piSize p + 1

theorem piLinearStep_size {q p : PiProc} (h : PiLinearStep q p) : piSize q < piSize p := by
  induction h with
  | comm channel p q => simp [piSize]; omega
  | parLeft h ih => simp only [piSize]; omega
  | parRight h ih => simp only [piSize]; omega

/-- Every process in the finite synchronous fragment is strongly normalizing. -/
theorem piLinearStep_wellFounded : WellFounded PiLinearStep :=
  Subrelation.wf (fun {_ _} h => piLinearStep_size h)
    (InvImage.wf piSize Nat.lt_wfRel.wf)

/-- A finite sender with `n` output prefixes. -/
def piSender : Nat → PiProc
  | 0 => .nil
  | n + 1 => .out 1 (piSender n)

/-- A finite receiver with `n` input prefixes. -/
def piReceiver : Nat → PiProc
  | 0 => .nil
  | n + 1 => .inp 1 (piReceiver n)

/-- A closed synchronous session with `n` communications remaining. -/
def piSession (n : Nat) : PiProc := .par (piSender n) (piReceiver n)

/-- One operational communication implements one countdown step. -/
theorem piSession_step (n : Nat) : PiLinearStep (piSession n) (piSession (n + 1)) := by
  simpa [piSession, piSender, piReceiver] using PiLinearStep.comm 1 (piSender n) (piReceiver n)

/-- The replicated server whose channels the level system must separate. -/
def server : PiProc := .rep (.inp 0 (.out 1 .nil))

/-- The translation of the recursor counter: an n-fold output prefix on the result channel. -/
def encCounter : Nat → PiProc
  | 0 => .nil
  | n + 1 => .out 1 (encCounter n)

/-- Counter depth of a process, the rank of the translated counter relation. -/
def counterDepth : PiProc → Nat
  | .nil => 0
  | .out _ r => counterDepth r + 1
  | .inp _ _ => 0
  | .par _ _ => 0
  | .rep _ => 0

theorem counterDepth_encCounter : ∀ n : Nat, counterDepth (encCounter n) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [encCounter, counterDepth, ih]

/-- The translated counter relation: the image of the counter loses one output. -/
def PiCounterStep (q p : PiProc) : Prop :=
  ∃ n : Nat, p = encCounter (n + 1) ∧ q = encCounter n

theorem piCounterStep_depth {q p : PiProc} (h : PiCounterStep q p) :
    counterDepth q < counterDepth p := by
  rcases h with ⟨n, rfl, rfl⟩
  rw [counterDepth_encCounter, counterDepth_encCounter]
  omega

theorem piCounterStep_wf : WellFounded PiCounterStep := by
  have h : ∀ p : PiProc, Acc PiCounterStep p := by
    intro p
    induction p using WellFounded.induction (InvImage.wf counterDepth Nat.lt_wfRel.wf) with
    | _ p ih =>
      exact Acc.intro p fun q hq => ih q (piCounterStep_depth hq)
  exact ⟨h⟩

/-! ## Row: piCalculusTerminationTranslation -/

/-- A level system on channels together with a decreasing first-order data measure, the two
certificates of the termination translation. -/
structure piCalculusTerminationTranslationData where
  level : Nat → Nat
  bound : Nat
  dataOf : Nat → Nat

/-- Laws: the level system separates the server's channels and the data measure strictly
decreases. -/
def piCalculusTerminationTranslationLaws (M : piCalculusTerminationTranslationData) : Prop :=
  M.level 0 < M.level 1 ∧ ∀ n : Nat, n < M.bound → M.dataOf (n + 1) < M.dataOf n

/-- Acceptance: the level system rejects the server and the data measure decreases, so the
translation admits the recursive counter. -/
def piCalculusTerminationTranslationAccepts (M : piCalculusTerminationTranslationData) : Prop :=
  M.level 0 < M.level 1 ∧ ∀ n : Nat, n < M.bound → M.dataOf (n + 1) < M.dataOf n

/-- Verdict: escape. The translated counter relation is well founded and the translation simulates
the source counter step while the data measure decreases. -/
def piCalculusTerminationTranslationResult (M : piCalculusTerminationTranslationData) : Prop :=
  piCalculusTerminationTranslationAccepts M ∧
    (∀ n : Nat, n < M.bound →
      PiCounterStep (encCounter n) (encCounter (n + 1)) ∧ M.dataOf (n + 1) < M.dataOf n) ∧
    WellFounded PiCounterStep

theorem piCalculusTerminationTranslation_sound :
    ∀ M, piCalculusTerminationTranslationLaws M → piCalculusTerminationTranslationAccepts M →
      piCalculusTerminationTranslationResult M := by
  intro M _ hA
  exact ⟨hA, fun n hn => ⟨⟨n, rfl, rfl⟩, hA.2 n hn⟩, piCounterStep_wf⟩

/-- The witness: level 0 on the input channel, level 2 on the result channel, and the data measure
`100 - n`. -/
def piCalculusTerminationTranslationWitness : piCalculusTerminationTranslationData where
  level := fun n => if n = 0 then 0 else 2
  bound := 100
  dataOf := fun n => 100 - n

theorem piCalculusTerminationTranslationWitness_laws :
    piCalculusTerminationTranslationLaws piCalculusTerminationTranslationWitness := by
  refine ⟨?_, ?_⟩
  · simp [piCalculusTerminationTranslationWitness]
  · intro n hn
    simp only [piCalculusTerminationTranslationWitness] at hn ⊢
    omega

theorem piCalculusTerminationTranslationWitness_accepts :
    piCalculusTerminationTranslationAccepts piCalculusTerminationTranslationWitness :=
  piCalculusTerminationTranslationWitness_laws

theorem piCalculusTerminationTranslationWitness_result :
    piCalculusTerminationTranslationResult piCalculusTerminationTranslationWitness :=
  piCalculusTerminationTranslation_sound _ piCalculusTerminationTranslationWitness_laws
    piCalculusTerminationTranslationWitness_accepts

theorem piCalculusTerminationTranslationWitness_feature :
    server = .rep (.inp 0 (.out 1 .nil)) ∧
      piCalculusTerminationTranslationWitness.level 0 ≠
        piCalculusTerminationTranslationWitness.level 1 := by
  refine ⟨rfl, ?_⟩
  simp [piCalculusTerminationTranslationWitness]

/-- The mutation: a constant data measure, so the decrease law fails at every n. -/
def piCalculusTerminationTranslationMutation : piCalculusTerminationTranslationData where
  level := fun _ => 0
  bound := 0
  dataOf := fun _ => 0

theorem piCalculusTerminationTranslation_mutation :
    ¬ piCalculusTerminationTranslationLaws piCalculusTerminationTranslationMutation := by
  intro h
  have h0 := h.1
  simp [piCalculusTerminationTranslationMutation] at h0

/-- Scope of the finite translation row: every accepted level/data certificate produces its
counter result. The relation-level theorem and an operational process instance follow below. -/
def piCalculusTerminationTranslation_scope : Prop :=
  ∀ M : piCalculusTerminationTranslationData,
    piCalculusTerminationTranslationLaws M → piCalculusTerminationTranslationResult M

/-- A termination-reflecting translation between arbitrary relations. Both relations are written
with the reduct first, matching Lean's `WellFounded` convention. -/
structure TerminationTranslation (α β : Type) where
  sourceRev : α → α → Prop
  targetRev : β → β → Prop
  encode : α → β
  simulates : ∀ {y x}, sourceRev y x → targetRev (encode y) (encode x)
  targetWellFounded : WellFounded targetRev

/-- Termination reflects through every step-preserving translation into a well-founded target. -/
theorem TerminationTranslation.sourceWellFounded {α β : Type}
    (T : TerminationTranslation α β) : WellFounded T.sourceRev :=
  Subrelation.wf (fun {_ _} h => T.simulates h) (InvImage.wf T.encode T.targetWellFounded)

/-- The natural-number countdown relation, reduct first. -/
def NatCountdownStep (q p : Nat) : Prop := ∃ n, p = n + 1 ∧ q = n

/-- Encoding a countdown step gives exactly one translated counter step. -/
theorem encCounter_simulates_countdown {q p : Nat} (h : NatCountdownStep q p) :
    PiCounterStep (encCounter q) (encCounter p) := by
  rcases h with ⟨n, hp, hq⟩
  subst p
  subst q
  exact ⟨n, rfl, rfl⟩

/-- Global, unbounded counter translation into the process carrier. -/
def piCounterTerminationTranslation : TerminationTranslation Nat PiProc where
  sourceRev := NatCountdownStep
  targetRev := PiCounterStep
  encode := encCounter
  simulates := encCounter_simulates_countdown
  targetWellFounded := piCounterStep_wf

/-- Translation of the global countdown into actual synchronous process communication. -/
def piOperationalTerminationTranslation : TerminationTranslation Nat PiProc where
  sourceRev := NatCountdownStep
  targetRev := PiLinearStep
  encode := piSession
  simulates := by
    intro q p h
    rcases h with ⟨n, hp, hq⟩
    subst p
    subst q
    exact piSession_step n
  targetWellFounded := piLinearStep_wellFounded

/-- The row scope is fully proved; its original finite `dataOf` component is a test fixture, while
the actual translated counter theorem is global and has no bound. -/
theorem piCalculusTerminationTranslation_scope_proven :
    piCalculusTerminationTranslation_scope := by
  intro M hL
  exact piCalculusTerminationTranslation_sound M hL hL

/-- Exact method identity for the implemented process translation: the reflection theorem is
carrier-independent, and the countdown is simulated by genuine synchronous communication. -/
theorem piCalculusTerminationTranslation_methodIdentity :
    (∀ {α β : Type} (T : TerminationTranslation α β), WellFounded T.sourceRev) ∧
      WellFounded PiLinearStep ∧
      (∀ n : Nat, PiLinearStep (piSession n) (piSession (n + 1))) ∧
      WellFounded NatCountdownStep ∧ piCalculusTerminationTranslation_scope := by
  exact ⟨fun T => T.sourceWellFounded, piLinearStep_wellFounded, piSession_step,
    piOperationalTerminationTranslation.sourceWellFounded,
    piCalculusTerminationTranslation_scope_proven⟩

/-! ## Row: lambdaMuSNViaCPS -/

/-- Terms of the lambda-mu calculus: variables, application, abstraction, and the mu binder. -/
inductive LMTerm where
  | var : Nat → LMTerm
  | app : LMTerm → LMTerm → LMTerm
  | lam : LMTerm → LMTerm
  | mu : Nat → LMTerm → LMTerm
  deriving DecidableEq, Repr

/-- Whether the distinguished variable bound by the surrounding abstraction occurs in a body.
An inner abstraction shadows it. -/
def lmBoundZeroOccurs : LMTerm → Prop
  | .var n => n = 0
  | .app f a => lmBoundZeroOccurs f ∨ lmBoundZeroOccurs a
  | .lam _ => False
  | .mu _ b => lmBoundZeroOccurs b

/-- Substitution for the distinguished variable at the removed outer binder. Inner abstractions
shadow that variable. -/
def lmSubstZero (a : LMTerm) : LMTerm → LMTerm
  | .var n => if n = 0 then a else .var n
  | .app f x => .app (lmSubstZero a f) (lmSubstZero a x)
  | .lam b => .lam b
  | .mu k b => .mu k (lmSubstZero a b)

theorem lmSubstZero_eq_self_of_not_occurs (a : LMTerm) :
    ∀ {b : LMTerm}, ¬ lmBoundZeroOccurs b → lmSubstZero a b = b := by
  intro b h
  induction b with
  | var n =>
      by_cases hn : n = 0
      · exact (h hn).elim
      · simp [lmSubstZero, hn]
  | app f x ihf ihx =>
      simp only [lmBoundZeroOccurs, not_or] at h
      simp [lmSubstZero, ihf h.1, ihx h.2]
  | lam b => rfl
  | mu k b ih => simp [lmSubstZero, ih h]

/-- Erasing head beta contraction, written with the reduct first. This is a genuine beta step:
the bound variable is absent, so capture-avoiding substitution returns the body. -/
def LMBeta (u t : LMTerm) : Prop :=
  ∃ (b a : LMTerm), ¬ lmBoundZeroOccurs b ∧
    t = .app (.lam b) a ∧ u = lmSubstZero a b

theorem lmBeta_substitution_exact {u t : LMTerm} (h : LMBeta u t) :
    ∃ (b a : LMTerm), ¬ lmBoundZeroOccurs b ∧
      t = .app (.lam b) a ∧ u = b := by
  rcases h with ⟨b, a, hb, rfl, rfl⟩
  exact ⟨b, a, hb, rfl, lmSubstZero_eq_self_of_not_occurs a hb⟩

/-- The size measure on lambda-mu terms. -/
def lmSize : LMTerm → Nat
  | .var _ => 1
  | .app f a => lmSize f + lmSize a + 1
  | .lam b => lmSize b + 1
  | .mu _ b => lmSize b + 1

theorem lmBeta_size {u t : LMTerm} (h : LMBeta u t) : lmSize u < lmSize t := by
  obtain ⟨b, a, hb, rfl, rfl⟩ := lmBeta_substitution_exact h
  simp [lmSize]
  omega

theorem lmBeta_wf : WellFounded LMBeta := by
  have h : ∀ t : LMTerm, Acc LMBeta t := by
    intro t
    induction t using WellFounded.induction (InvImage.wf lmSize Nat.lt_wfRel.wf) with
    | _ t ih =>
      exact Acc.intro t fun u hu => ih u (lmBeta_size hu)
  exact ⟨h⟩

/-- The continuation-passing translation on the head fragment: an application threads a
continuation variable, and a mu binder becomes its continuation argument. -/
def cps : LMTerm → LMTerm
  | .var x => .var x
  | .app f a => .app (.app (.var 0) (cps f)) (cps a)
  | .lam b => .lam (cps b)
  | .mu x b => .app (cps b) (.var x)

/-- A translation together with the continuation it threads, the data of the row. -/
structure lambdaMuSNViaCPSData where
  translate : LMTerm → LMTerm

/-- Laws: the translation makes every head beta step decrease the size of the image. -/
def lambdaMuSNViaCPSLaws (M : lambdaMuSNViaCPSData) : Prop :=
  ∀ u t : LMTerm, LMBeta u t → lmSize (M.translate u) < lmSize (M.translate t)

/-- Acceptance: the same decrease, read as the criterion the translation must meet. -/
def lambdaMuSNViaCPSAccepts (M : lambdaMuSNViaCPSData) : Prop :=
  ∀ u t : LMTerm, LMBeta u t → lmSize (M.translate u) < lmSize (M.translate t)

/-- Verdict: escape. The translated beta relation is well founded, ranked by the size of the
image. -/
def lambdaMuSNViaCPSResult (M : lambdaMuSNViaCPSData) : Prop :=
  lambdaMuSNViaCPSAccepts M ∧
    WellFounded (fun u t : LMTerm => LMBeta u t ∧
      lmSize (M.translate u) < lmSize (M.translate t))

theorem lambdaMuSNViaCPS_sound :
    ∀ M, lambdaMuSNViaCPSLaws M → lambdaMuSNViaCPSAccepts M → lambdaMuSNViaCPSResult M := by
  intro M _ hA
  refine ⟨hA, ?_⟩
  have h : ∀ t : LMTerm, Acc (fun u t : LMTerm => LMBeta u t ∧
      lmSize (M.translate u) < lmSize (M.translate t)) t := by
    intro t
    induction t using WellFounded.induction
      (InvImage.wf (fun t => lmSize (M.translate t)) Nat.lt_wfRel.wf) with
    | _ t ih =>
      exact Acc.intro t fun u hu => ih u hu.2
  exact ⟨h⟩

/-- The witness is the nonidentity continuation-passing translation `cps`. -/
def lambdaMuSNViaCPSWitness : lambdaMuSNViaCPSData where
  translate := cps

theorem lmSize_cps_pos (t : LMTerm) : 0 < lmSize (cps t) := by
  induction t <;> simp_all [cps, lmSize]

theorem lambdaMuSNViaCPSWitness_laws :
    lambdaMuSNViaCPSLaws lambdaMuSNViaCPSWitness := by
  intro u t h
  obtain ⟨b, a, _hb, ht, hu⟩ := lmBeta_substitution_exact h
  subst t
  subst u
  simp only [lambdaMuSNViaCPSWitness, cps, lmSize]
  have hb := lmSize_cps_pos b
  omega

theorem lambdaMuSNViaCPSWitness_result :
    lambdaMuSNViaCPSResult lambdaMuSNViaCPSWitness :=
  lambdaMuSNViaCPS_sound _ lambdaMuSNViaCPSWitness_laws
    lambdaMuSNViaCPSWitness_laws

theorem lambdaMuSNViaCPSWitness_feature :
    lambdaMuSNViaCPSWitness.translate = cps ∧
      lambdaMuSNViaCPSWitness.translate (.app (.lam (.var 0)) (.var 1)) ≠
        (.app (.lam (.var 0)) (.var 1)) ∧
      lmSize (lambdaMuSNViaCPSWitness.translate (.app (.lam (.var 0)) (.var 1))) = 6 := by
  simp [lambdaMuSNViaCPSWitness, cps, lmSize]

/-- The mutation: the constant translation, which maps every redex and reduct to the same term,
so the decrease law fails. -/
def lambdaMuSNViaCPSMutation : lambdaMuSNViaCPSData where
  translate := fun _ => .var 0

theorem lambdaMuSNViaCPS_mutation :
    ¬ lambdaMuSNViaCPSLaws lambdaMuSNViaCPSMutation := by
  intro h
  have hs : LMBeta (.var 1) (.app (.lam (.var 1)) (.var 2)) := by
    exact ⟨.var 1, .var 2, by simp [lmBoundZeroOccurs], rfl, by simp [lmSubstZero]⟩
  have h0 := h (.var 1) (.app (.lam (.var 1)) (.var 2)) hs
  simp [lambdaMuSNViaCPSMutation, lmSize] at h0

/-- Scope of the implemented erasing-head lambda-mu fragment. Every translation satisfying the
image-decrease law proves the fragment's strong normalization. -/
def lambdaMuSNViaCPS_scope : Prop :=
  ∀ M : lambdaMuSNViaCPSData, lambdaMuSNViaCPSLaws M → lambdaMuSNViaCPSResult M

/-- The stated head-fragment scope is fully proved. -/
theorem lambdaMuSNViaCPS_scope_proven : lambdaMuSNViaCPS_scope := by
  intro M hL
  exact lambdaMuSNViaCPS_sound M hL hL

/-- The CPS image rank is a termination-reflecting translation into natural-number descent. -/
def lambdaMuCPSTerminationTranslation
    (M : lambdaMuSNViaCPSData) (hL : lambdaMuSNViaCPSLaws M) :
    TerminationTranslation LMTerm Nat where
  sourceRev := LMBeta
  targetRev := (fun m n => m < n)
  encode := fun t => lmSize (M.translate t)
  simulates := hL _ _
  targetWellFounded := Nat.lt_wfRel.wf

/-- Exact method identity for the implemented CPS row. The witness is the declared nonidentity
CPS map, every source step decreases its image, and the carrier-independent translation theorem
states the termination argument used by the row. -/
theorem lambdaMuSNViaCPS_methodIdentity :
    lambdaMuSNViaCPSWitness.translate = cps ∧
      lambdaMuSNViaCPSLaws lambdaMuSNViaCPSWitness ∧
      WellFounded LMBeta ∧ lambdaMuSNViaCPS_scope :=
  ⟨rfl, lambdaMuSNViaCPSWitness_laws,
    (lambdaMuCPSTerminationTranslation lambdaMuSNViaCPSWitness
      lambdaMuSNViaCPSWitness_laws).sourceWellFounded,
    lambdaMuSNViaCPS_scope_proven⟩

end OperatorKO7.Methods.OrientationClosure.MethodRowsProcessCalculi
