import OperatorKO7.Meta.UniqueNormalization.ConditionalTRS

/-!
# Faithful condition histories as data

Campaign: `COMMAND-CENTER/design/RESEARCH-ROADMAP.md`, package DC-5 of the Distinction
certificate closeout.

The conditional step relation `CStepLevel` of `ConditionalTRS.lean` lives in `Prop`: two proofs of
one step or conversion are equal, so a proof records no count of the steps it uses. This module
stores the derivation itself as data. `TraceData` is a finite path that keeps every step
occurrence, repeated uses of identical data included; `SignedData` orients a step. A guarded root
record (`GuardedRootData`) stores the actual rule, its membership, the substitution, both endpoint
equations, and one history per condition slot, indexed by `Fin rule.conds.length`, so equal
conditions occupy separate slots. `ContextStepData` closes it under argument contexts, and
`LevelStepData` stratifies it exactly as `CStepLevel` does: level `0` is empty and a level `n + 1`
root record carries histories of level-`n` steps.

The data are faithful: nonemptiness of the data is equivalent to the existing relation at every
level (`levelStepData_iff`, `levelConvData_iff`) and, through a common finite level, to conditional
conversion (`conditionalHistory_iff_cconv`). Reversal and concatenation are constructed with their
endpoint and length laws; the outer path length is distinguished from the count of all step
occurrences, nested condition histories included (`history_totalOccurrences`). Two placements of
one step are two list entries (`history_occurrence_reuse`), while the erased proofs are equal, so
no function of the erased proof recovers a step count (`history_erasure_not_injective`). A history
built from steps inside one argument position projects to that argument; a root step between
terms of the same shape does not (`context_history_projection`,
`root_history_projection_fails`).

Proves: the correspondence between the data and the existing conditional semantics, and the
history operations and controls listed above.
Does not prove: any reconstruction step of H3.3, any decomposition of arbitrary conversions, or a
decreasing measure.
Relation: `CStepLevel C n`, `relConv (CStepLevel C n)` and `cconv C`.
Closure: one conditional step; conversion.
Strategy: full rewriting.
Trust: kernel checked; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe` or
`opaque`. `Classical.choice` enters where a proposition supplies nonempty data for a condition
slot. Axiom footprints are printed by the paired reach file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.ConditionHistory

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v w x y

/-! ## Finite traces and oriented steps -/

section Generic

variable {A : Type w}

/-- An oriented step: forward, or backward along a step in the other direction. -/
inductive SignedData (E : A → A → Type x) : A → A → Type (max w x) where
  | forward {a b : A} : E a b → SignedData E a b
  | backward {a b : A} : E b a → SignedData E a b

/-- A finite path from `a`; every step occurrence is stored, repeated identical steps included.
The start point is a parameter. Each recursive function below binds it before the colon, so it stays
fixed across recursive calls and the recursion is structural. -/
inductive TraceData (E : A → A → Type x) (a : A) : A → Type (max w x) where
  | nil : TraceData E a a
  | snoc {b c : A} : TraceData E a b → E b c → TraceData E a c

/-- Data whose nonemptiness is exactly a relation. -/
def FaithfulData (E : A → A → Type x) (r : A → A → Prop) : Prop :=
  ∀ a b, Nonempty (E a b) ↔ r a b

namespace SignedData

variable {E : A → A → Type x}

/-- Reverse the orientation. -/
def flip : {a b : A} → SignedData E a b → SignedData E b a
  | _, _, forward e => backward e
  | _, _, backward e => forward e

/-- Map the underlying steps. -/
def map {E' : A → A → Type y} (φ : ∀ a b, E a b → E' a b) :
    {a b : A} → SignedData E a b → SignedData E' a b
  | _, _, forward e => forward (φ _ _ e)
  | _, _, backward e => backward (φ _ _ e)

/-- A weight read off the underlying step. -/
def weight (wt : ∀ a b, E a b → Nat) : {a b : A} → SignedData E a b → Nat
  | _, _, forward e => wt _ _ e
  | _, _, backward e => wt _ _ e

end SignedData

namespace TraceData

variable {E : A → A → Type x}

/-- The number of step occurrences on the outer path. -/
def length {a : A} : {b : A} → TraceData E a b → Nat
  | _, nil => 0
  | _, snoc tr _ => tr.length + 1

/-- Concatenation. -/
def append {a b : A} (tr : TraceData E a b) : {c : A} → TraceData E b c → TraceData E a c
  | _, nil => tr
  | _, snoc tr' e => snoc (append tr tr') e

/-- Prepend one step. -/
def cons {a b : A} (e : E a b) : {c : A} → TraceData E b c → TraceData E a c
  | _, nil => snoc nil e
  | _, snoc tr e' => snoc (cons e tr) e'

/-- Map the steps, keeping the endpoints. -/
def map {E' : A → A → Type y} (φ : ∀ a b, E a b → E' a b) {a : A} :
    {b : A} → TraceData E a b → TraceData E' a b
  | _, nil => nil
  | _, snoc tr e => snoc (map φ tr) (φ _ _ e)

/-- Map the steps along a map of endpoints. -/
def mapIdx {B : Type y} {F : B → B → Type x} (g : A → B) (φ : ∀ a b, E a b → F (g a) (g b))
    {a : A} : {b : A} → TraceData E a b → TraceData F (g a) (g b)
  | _, nil => nil
  | _, snoc tr e => snoc (mapIdx g φ tr) (φ _ _ e)

/-- The total weight of the step occurrences. -/
def sumWeights (wt : ∀ a b, E a b → Nat) {a : A} : {b : A} → TraceData E a b → Nat
  | _, nil => 0
  | _, snoc tr e => sumWeights wt tr + wt _ _ e

/-- The step occurrences in order, one list entry per occurrence. -/
def steps {a : A} : {b : A} → TraceData E a b → List ((p : A) × (q : A) × E p q)
  | _, nil => []
  | _, snoc tr e => tr.steps ++ [⟨_, _, e⟩]

/-- **The length of a concatenation.** -/
theorem length_append {a b : A} (x : TraceData E a b) : ∀ {c : A} (z : TraceData E b c),
    (append x z).length = x.length + z.length
  | _, nil => rfl
  | _, snoc z _ => by
      simp only [append, length, length_append x z]
      omega

/-- The length of a prepended trace. -/
theorem length_cons {a b : A} (e : E a b) : ∀ {c : A} (tr : TraceData E b c),
    (cons e tr).length = tr.length + 1
  | _, nil => rfl
  | _, snoc tr _ => by
      simp only [cons, length, length_cons e tr]

/-- Mapping keeps the length. -/
theorem length_map {E' : A → A → Type y} (φ : ∀ a b, E a b → E' a b) {a : A} :
    ∀ {b : A} (tr : TraceData E a b), (map φ tr).length = tr.length
  | _, nil => rfl
  | _, snoc tr _ => by simp only [map, length, length_map φ tr]

/-- Mapping along endpoints keeps the length. -/
theorem length_mapIdx {B : Type y} {F : B → B → Type x} (g : A → B)
    (φ : ∀ a b, E a b → F (g a) (g b)) {a : A} :
    ∀ {b : A} (tr : TraceData E a b), (mapIdx g φ tr).length = tr.length
  | _, nil => rfl
  | _, snoc tr _ => by simp only [mapIdx, length, length_mapIdx g φ tr]

/-- The step list has one entry per outer step. -/
theorem steps_length {a : A} : ∀ {b : A} (tr : TraceData E a b), tr.steps.length = tr.length
  | _, nil => rfl
  | _, snoc tr _ => by simp [steps, length, steps_length tr]

/-- **A trace is sound for the relation its steps imply.** -/
theorem sound {r : A → A → Prop} (hE : ∀ a b, E a b → r a b) {a : A} :
    ∀ {b : A}, TraceData E a b → Relation.ReflTransGen r a b
  | _, nil => Relation.ReflTransGen.refl
  | _, snoc tr e => Relation.ReflTransGen.tail (sound hE tr) (hE _ _ e)

end TraceData

namespace TraceData

variable {E : A → A → Type x}

/-- **Reversal of an oriented trace.** -/
def reverse {a : A} : {b : A} → TraceData (SignedData E) a b → TraceData (SignedData E) b a
  | _, nil => nil
  | _, snoc tr s => cons s.flip (reverse tr)

/-- **The length of a reversal.** -/
theorem length_reverse {a : A} : ∀ {b : A} (tr : TraceData (SignedData E) a b),
    tr.reverse.length = tr.length
  | _, nil => rfl
  | _, snoc tr _ => by simp only [reverse, length, length_cons, length_reverse tr]

end TraceData

/-- **Faithful steps give faithful traces.** -/
theorem traceData_faithful {E : A → A → Type x} {r : A → A → Prop} (hf : FaithfulData E r) :
    FaithfulData (TraceData E) (Relation.ReflTransGen r) := by
  intro a b
  constructor
  · rintro ⟨tr⟩
    exact TraceData.sound (fun a b e => (hf a b).1 ⟨e⟩) tr
  · intro h
    induction h with
    | refl => exact ⟨TraceData.nil⟩
    | tail _ hbc ih =>
        obtain ⟨tr⟩ := ih
        obtain ⟨e⟩ := (hf _ _).2 hbc
        exact ⟨TraceData.snoc tr e⟩

/-- **Faithful steps give faithful oriented steps.** -/
theorem signedData_faithful {E : A → A → Type x} {r : A → A → Prop} (hf : FaithfulData E r) :
    FaithfulData (SignedData E) (fun a b => r a b ∨ r b a) := by
  intro a b
  constructor
  · rintro ⟨s⟩
    cases s with
    | forward e => exact Or.inl ((hf _ _).1 ⟨e⟩)
    | backward e => exact Or.inr ((hf _ _).1 ⟨e⟩)
  · rintro (h | h)
    · obtain ⟨e⟩ := (hf _ _).2 h
      exact ⟨SignedData.forward e⟩
    · obtain ⟨e⟩ := (hf _ _).2 h
      exact ⟨SignedData.backward e⟩

/-- **Faithful steps give faithful conversion histories.** -/
theorem convData_faithful {E : A → A → Type x} {r : A → A → Prop} (hf : FaithfulData E r) :
    FaithfulData (TraceData (SignedData E)) (relConv r) :=
  traceData_faithful (signedData_faithful hf)

/-- **Occurrences of identical data are stored separately.** The trace `a → a → a` using one step
twice has two list entries at different positions holding the same step, and its total weight counts
both; any two proofs of the erased proposition are equal. -/
theorem history_occurrence_reuse {E : A → A → Type x} {a : A} (e : E a a)
    (wt : ∀ p q, E p q → Nat) {r : A → A → Prop} :
    (TraceData.snoc (TraceData.snoc (TraceData.nil (a := a)) e) e).steps = [⟨a, a, e⟩, ⟨a, a, e⟩] ∧
      (TraceData.snoc (TraceData.snoc (TraceData.nil (a := a)) e) e).length = 2 ∧
      (TraceData.snoc (TraceData.snoc (TraceData.nil (a := a)) e) e).sumWeights wt = 2 * wt a a e ∧
      ∀ p q : Relation.ReflTransGen r a a, p = q := by
  refine ⟨rfl, rfl, ?_, fun _ _ => rfl⟩
  simp only [TraceData.sumWeights]
  omega

end Generic

/-! ## Conditional derivation data -/

section Conditional

variable {sigma : Type u} {nu : Type v}

/-- **A guarded root step as data**: the rule, its membership, the substitution, both endpoint
equations, and one history per condition slot. -/
structure GuardedRootData (C : CTRS sigma nu)
    (H : Term sigma nu → Term sigma nu → Type (max u v)) (s t : Term sigma nu) :
    Type (max u v) where
  /-- The fired rule. -/
  rule : CRule sigma nu
  /-- The rule belongs to the system. -/
  mem : rule ∈ C
  /-- The matching substitution. -/
  subst : Subst sigma nu
  /-- The source is the instance of the left-hand side. -/
  src : s = Subst.apply subst rule.lhs
  /-- The target is the instance of the right-hand side. -/
  tgt : t = Subst.apply subst rule.rhs
  /-- One history per condition slot. -/
  history : (i : Fin rule.conds.length) →
    H (Subst.apply subst (rule.conds.get i).1) (Subst.apply subst (rule.conds.get i).2)

/-- **Contextual closure of guarded root data.** -/
inductive ContextStepData (C : CTRS sigma nu)
    (H : Term sigma nu → Term sigma nu → Type (max u v)) :
    Term sigma nu → Term sigma nu → Type (max u v) where
  | root {s t : Term sigma nu} : GuardedRootData C H s t → ContextStepData C H s t
  | arg (f : sigma) (pre post : List (Term sigma nu)) {a b : Term sigma nu} :
      ContextStepData C H a b →
      ContextStepData C H (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- **Level-stratified step data.** Level `0` is empty; a level `n + 1` step stores histories of
level-`n` steps for its conditions, exactly as `CStepLevel` does. -/
def LevelStepData (C : CTRS sigma nu) : Nat → Term sigma nu → Term sigma nu → Type (max u v)
  | 0 => fun _ _ => PEmpty.{max u v + 1}
  | n + 1 => ContextStepData C (TraceData (SignedData (LevelStepData C n)))

/-- **Faithful condition histories give faithful contextual steps.** Membership of a condition
yields its slot; conversely a proposition supplies nonempty data for each slot. -/
theorem contextStepData_faithful {C : CTRS sigma nu}
    {H : Term sigma nu → Term sigma nu → Type (max u v)}
    {E : Term sigma nu → Term sigma nu → Prop} (hH : FaithfulData H E) :
    FaithfulData (ContextStepData C H) (CStepE C E) := by
  intro s t
  constructor
  · rintro ⟨d⟩
    induction d with
    | root g =>
        refine CStepE.root ⟨g.rule, g.mem, g.subst, g.src, g.tgt, ?_⟩
        intro p hp
        obtain ⟨i, rfl⟩ := List.get_of_mem hp
        exact (hH _ _).1 ⟨g.history i⟩
    | arg f pre post _ ih => exact CStepE.arg f pre post ih
  · intro h
    induction h with
    | root hr =>
        obtain ⟨crule, hmem, σ, hs, ht, hconds⟩ := hr
        exact ⟨ContextStepData.root ⟨crule, hmem, σ, hs, ht,
          fun i => Classical.choice ((hH _ _).2 (hconds _ (List.get_mem _ i)))⟩⟩
    | arg f pre post _ ih =>
        obtain ⟨d⟩ := ih
        exact ⟨ContextStepData.arg f pre post d⟩

/-- **Level data are faithful to `CStepLevel` at every level.** -/
theorem levelStepData_iff (C : CTRS sigma nu) :
    ∀ (n : Nat) (s t : Term sigma nu), Nonempty (LevelStepData C n s t) ↔ CStepLevel C n s t
  | 0, _, _ => ⟨fun ⟨d⟩ => PEmpty.elim d, fun h => h.elim⟩
  | n + 1, s, t =>
      contextStepData_faithful (C := C) (convData_faithful (levelStepData_iff C n)) s t

/-- **Level conversion histories are faithful to level conversion.** -/
theorem levelConvData_iff (C : CTRS sigma nu) (n : Nat) (s t : Term sigma nu) :
    Nonempty (TraceData (SignedData (LevelStepData C n)) s t) ↔ relConv (CStepLevel C n) s t :=
  convData_faithful (levelStepData_iff C n) s t

/-- A conversion of the conditional system uses finitely many levels, hence a common one. -/
theorem cconv_exists_level {C : CTRS sigma nu} {s t : Term sigma nu} (h : cconv C s t) :
    ∃ n, relConv (CStepLevel C n) s t := by
  induction h with
  | refl => exact ⟨0, relConv.refl _⟩
  | tail _ hlast ih =>
      obtain ⟨n, hn⟩ := ih
      have hlift : ∀ {k : Nat} {p q : Term sigma nu}, k ≤ max n k →
          CStepLevel C k p q → CStepLevel C (max n k) p q :=
        fun hk h => CStepLevel.mono_of_le C hk h
      rcases hlast with ⟨m, hm⟩ | ⟨m, hm⟩
      · refine ⟨max n m, relConv.trans ?_ (relConv.single (hlift (le_max_right n m) hm))⟩
        exact relConv.mono (fun _ _ hab => CStepLevel.mono_of_le C (le_max_left n m) hab) hn
      · refine ⟨max n m, relConv.trans ?_
          (relConv.symm (relConv.single (hlift (le_max_right n m) hm)))⟩
        exact relConv.mono (fun _ _ hab => CStepLevel.mono_of_le C (le_max_left n m) hab) hn

/-- **A conditional history**: a level and a conversion history at that level. -/
def ConditionalHistory (C : CTRS sigma nu) (s t : Term sigma nu) : Type (max u v) :=
  (n : Nat) × TraceData (SignedData (LevelStepData C n)) s t

/-- **Conditional histories are faithful to conditional conversion.** -/
theorem conditionalHistory_iff_cconv (C : CTRS sigma nu) (s t : Term sigma nu) :
    Nonempty (ConditionalHistory C s t) ↔ cconv C s t := by
  constructor
  · rintro ⟨⟨n, tr⟩⟩
    exact relConv.mono (fun _ _ hab => CStep.of_level hab) ((levelConvData_iff C n s t).1 ⟨tr⟩)
  · intro h
    obtain ⟨n, hn⟩ := cconv_exists_level h
    obtain ⟨tr⟩ := (levelConvData_iff C n s t).2 hn
    exact ⟨⟨n, tr⟩⟩

/-! ### Mapping, lifting and counting -/

/-- Map the condition histories of contextual step data. -/
def ContextStepData.mapHistory {C : CTRS sigma nu}
    {H H' : Term sigma nu → Term sigma nu → Type (max u v)} (φ : ∀ a b, H a b → H' a b) :
    {s t : Term sigma nu} → ContextStepData C H s t → ContextStepData C H' s t
  | _, _, root g => root ⟨g.rule, g.mem, g.subst, g.src, g.tgt, fun i => φ _ _ (g.history i)⟩
  | _, _, arg f pre post d => arg f pre post (mapHistory φ d)

/-- The weight of contextual step data: one for the root record plus the weights of its condition
histories. -/
def ContextStepData.weight {C : CTRS sigma nu}
    {H : Term sigma nu → Term sigma nu → Type (max u v)} (hw : ∀ a b, H a b → Nat) :
    {s t : Term sigma nu} → ContextStepData C H s t → Nat
  | _, _, root g => 1 + ((List.finRange g.rule.conds.length).map (fun i => hw _ _ (g.history i))).sum
  | _, _, arg _ _ _ d => weight hw d

/-- **One level up.** -/
def LevelStepData.liftSucc (C : CTRS sigma nu) :
    ∀ (n : Nat) {s t : Term sigma nu}, LevelStepData C n s t → LevelStepData C (n + 1) s t
  | 0, _, _, d => PEmpty.elim d
  | n + 1, _, _, d =>
      ContextStepData.mapHistory
        (fun _ _ tr => TraceData.map (fun _ _ sd => SignedData.map
          (fun _ _ e => LevelStepData.liftSucc C n e) sd) tr) d

/-- **Along any level inequality.** -/
def LevelStepData.liftLE (C : CTRS sigma nu) {m n : Nat} (h : m ≤ n) {s t : Term sigma nu}
    (d : LevelStepData C m s t) : LevelStepData C n s t :=
  Nat.leRecOn (C := fun k => LevelStepData C k s t) h (fun {k} e => LevelStepData.liftSucc C k e) d

/-- **All step occurrences**, the root records of nested condition histories included. -/
def LevelStepData.occurrences (C : CTRS sigma nu) :
    ∀ (n : Nat) {s t : Term sigma nu}, LevelStepData C n s t → Nat
  | 0, _, _, d => PEmpty.elim d
  | n + 1, _, _, d =>
      ContextStepData.weight
        (fun _ _ tr => TraceData.sumWeights (fun _ _ sd => SignedData.weight
          (fun _ _ e => LevelStepData.occurrences C n e) sd) tr) d

namespace ConditionalHistory

variable {C : CTRS sigma nu}

/-- The outer path length. -/
def length {s t : Term sigma nu} (h : ConditionalHistory C s t) : Nat := h.2.length

/-- The count of all step occurrences, nested condition histories included. -/
def totalOccurrences {s t : Term sigma nu} (h : ConditionalHistory C s t) : Nat :=
  h.2.sumWeights (fun _ _ sd => SignedData.weight (fun _ _ e => LevelStepData.occurrences C h.1 e) sd)

/-- **Reversal.** -/
def reverse {s t : Term sigma nu} (h : ConditionalHistory C s t) : ConditionalHistory C t s :=
  ⟨h.1, h.2.reverse⟩

/-- **Concatenation**, at the larger of the two levels. -/
def append {a b c : Term sigma nu} (h₁ : ConditionalHistory C a b)
    (h₂ : ConditionalHistory C b c) : ConditionalHistory C a c :=
  ⟨max h₁.1 h₂.1,
    TraceData.append
      (h₁.2.map (fun _ _ sd => sd.map (fun _ _ e => LevelStepData.liftLE C (le_max_left _ _) e)))
      (h₂.2.map (fun _ _ sd => sd.map (fun _ _ e => LevelStepData.liftLE C (le_max_right _ _) e)))⟩

end ConditionalHistory

/-- **Reversal keeps the outer length and swaps the endpoints.** -/
theorem history_reverse {C : CTRS sigma nu} {s t : Term sigma nu} (h : ConditionalHistory C s t) :
    h.reverse.length = h.length ∧ cconv C t s :=
  ⟨TraceData.length_reverse h.2, (conditionalHistory_iff_cconv C t s).1 ⟨h.reverse⟩⟩

/-- **Concatenation joins the endpoints.** -/
theorem history_append {C : CTRS sigma nu} {a b c : Term sigma nu}
    (h₁ : ConditionalHistory C a b) (h₂ : ConditionalHistory C b c) :
    cconv C a c :=
  (conditionalHistory_iff_cconv C a c).1 ⟨h₁.append h₂⟩

/-- **The outer length of a concatenation is the sum of the outer lengths.** -/
theorem history_length_append {C : CTRS sigma nu} {a b c : Term sigma nu}
    (h₁ : ConditionalHistory C a b) (h₂ : ConditionalHistory C b c) :
    (h₁.append h₂).length = h₁.length + h₂.length := by
  simp only [ConditionalHistory.length, ConditionalHistory.append, TraceData.length_append,
    TraceData.length_map]

/-- Every step of positive level counts at least itself. -/
theorem occurrences_pos (C : CTRS sigma nu) (n : Nat) :
    ∀ {s t : Term sigma nu} (d : LevelStepData C (n + 1) s t), 1 ≤ LevelStepData.occurrences C (n + 1) d := by
  intro s t d
  change ContextStepData C (TraceData (SignedData (LevelStepData C n))) s t at d
  induction d with
  | root g =>
      show 1 ≤ 1 + _
      omega
  | arg f pre post d ih => exact ih

/-- The outer length never exceeds the occurrence count. -/
theorem length_le_totalOccurrences {C : CTRS sigma nu} {s t : Term sigma nu}
    (h : ConditionalHistory C s t) : h.length ≤ h.totalOccurrences := by
  obtain ⟨n, tr⟩ := h
  simp only [ConditionalHistory.length, ConditionalHistory.totalOccurrences]
  induction tr with
  | nil => exact Nat.le_refl _
  | snoc tr sd ih =>
      simp only [TraceData.length, TraceData.sumWeights]
      have hsd : 1 ≤ SignedData.weight (fun _ _ e => LevelStepData.occurrences C n e) sd := by
        cases n with
        | zero =>
            cases sd with
            | forward e => exact PEmpty.elim e
            | backward e => exact PEmpty.elim e
        | succ n =>
            cases sd with
            | forward e => exact occurrences_pos C n e
            | backward e => exact occurrences_pos C n e
      omega

end Conditional

/-! ## Fixtures -/

section Fixtures

open CondExample

/-- The level-1 step `b → c` of `CondExample.demoCTRS`, as data: the rule has no condition. -/
def stepBC : LevelStepData demoCTRS 1 (.app 0 []) (.app 1 []) :=
  ContextStepData.root ⟨crB, List.Mem.head _, subBC, rfl, rfl, fun i => Fin.elim0 i⟩

/-- The level-2 step `f(b, c) → a`, whose one condition slot holds the history `b → c`. -/
def stepFBCA : LevelStepData demoCTRS 2 (.app 2 [.app 0 [], .app 1 []]) (.app 3 []) :=
  ContextStepData.root ⟨crF, List.Mem.tail _ (List.Mem.head _), subBC, rfl, rfl,
    fun i => Fin.cases (motive := fun i : Fin 1 =>
        TraceData (SignedData (LevelStepData demoCTRS 1))
          (Subst.apply subBC (crF.conds.get i).1) (Subst.apply subBC (crF.conds.get i).2))
      (TraceData.snoc TraceData.nil (SignedData.forward stepBC)) (fun j => Fin.elim0 j) i⟩

/-- The one-step conditional history of `f(b, c) → a`. -/
def historyFBCA : ConditionalHistory demoCTRS (.app 2 [.app 0 [], .app 1 []]) (.app 3 []) :=
  ⟨2, TraceData.snoc TraceData.nil (SignedData.forward stepFBCA)⟩

/-- **Outer length and total occurrences differ**: the level-2 step counts itself and the nested
step `b → c` of its condition history. -/
theorem history_totalOccurrences :
    historyFBCA.length = 1 ∧ historyFBCA.totalOccurrences = 2 ∧
      ∀ {s t : Term Nat Nat} (h : ConditionalHistory demoCTRS s t), h.length ≤ h.totalOccurrences :=
  ⟨rfl, rfl, fun h => length_le_totalOccurrences h⟩

/-- The empty history at `b`. -/
def emptyAtB : TraceData (SignedData (LevelStepData demoCTRS 1)) (.app 0 []) (.app 0 []) :=
  TraceData.nil

/-- The history `b → c → b`. -/
def loopAtB : TraceData (SignedData (LevelStepData demoCTRS 1)) (.app 0 []) (.app 0 []) :=
  TraceData.snoc (TraceData.snoc TraceData.nil (SignedData.forward stepBC))
    (SignedData.backward stepBC)

/-- **Erasure is not injective**: the empty history at `b` and the history `b → c → b` erase to the
same proof of the conversion, with outer lengths `0` and `2`; so no function of the erased proof
recovers the step count. -/
theorem history_erasure_not_injective :
    emptyAtB.length = 0 ∧ loopAtB.length = 2 ∧
      (levelConvData_iff demoCTRS 1 _ _).1 ⟨emptyAtB⟩ =
        (levelConvData_iff demoCTRS 1 _ _).1 ⟨loopAtB⟩ ∧
      ¬ ∃ count : relConv (CStepLevel demoCTRS 1) (.app 0 []) (.app 0 []) → Nat,
        ∀ tr : TraceData (SignedData (LevelStepData demoCTRS 1)) (.app 0 []) (.app 0 []),
          count ((levelConvData_iff demoCTRS 1 _ _).1 ⟨tr⟩) = tr.length := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rintro ⟨count, hcount⟩
  -- the two erased proofs are equal, so the two counts agree
  have h02 : (0 : Nat) = 2 := (hcount emptyAtB).symm.trans (hcount loopAtB)
  exact absurd h02 (by decide)

end Fixtures

/-! ## Projection to an argument position -/

section Projection

variable {sigma : Type u} {nu : Type v}

/-- A history lifted into argument position `pre.length` of `f`: every step is a context step at that
position. -/
def liftArgTrace {C : CTRS sigma nu} (n : Nat) (f : sigma) (pre post : List (Term sigma nu))
    {a b : Term sigma nu} (tr : TraceData (SignedData (LevelStepData C (n + 1))) a b) :
    TraceData (SignedData (LevelStepData C (n + 1)))
      (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) :=
  TraceData.mapIdx (E := SignedData (LevelStepData C (n + 1)))
    (F := SignedData (LevelStepData C (n + 1))) (fun z => Term.app f (pre ++ z :: post))
    (fun _ _ sd => match sd with
      | SignedData.forward e => SignedData.forward (ContextStepData.arg f pre post e)
      | SignedData.backward e => SignedData.backward (ContextStepData.arg f pre post e)) tr

/-- **Projection under the origin condition.** A history that is the lifting of a history `inner`
between the arguments (the origin condition) has the same outer length as `inner`, and `inner`
converts the arguments at the same level. -/
theorem context_history_projection {C : CTRS sigma nu} (n : Nat) (f : sigma)
    (pre post : List (Term sigma nu)) {a b : Term sigma nu}
    (hist : TraceData (SignedData (LevelStepData C (n + 1)))
      (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)))
    (inner : TraceData (SignedData (LevelStepData C (n + 1))) a b)
    (horigin : hist = liftArgTrace n f pre post inner) :
    hist.length = inner.length ∧ relConv (CStepLevel C (n + 1)) a b := by
  refine ⟨?_, (levelConvData_iff C (n + 1) a b).1 ⟨inner⟩⟩
  rw [horigin]
  unfold liftArgTrace
  exact TraceData.length_mapIdx _ _ inner

/-- The root-rewriting control: `F(c) → F(d)`, with `F = 0`, `c = 1`, `d = 2`. -/
def rootOnly : CTRS Nat Nat := [⟨.app 0 [.app 1 []], .app 0 [.app 2 []], [], rfl⟩]

/-- `c` has no conditional step in either direction. -/
theorem rootOnly_c_isolated : ∀ (n : Nat) (w : Term Nat Nat),
    ¬ CStepLevel rootOnly n (.app 1 []) w ∧ ¬ CStepLevel rootOnly n w (.app 1 []) := by
  intro n w
  cases n with
  | zero => exact ⟨id, id⟩
  | succ n =>
      constructor
      · intro h
        rcases CStepE.app_inv h with ⟨crule, hmem, σ, hs, -, -⟩ | ⟨pre, post, p, q, hargs, -, -⟩
        · simp only [rootOnly, List.mem_singleton] at hmem
          subst hmem
          simp at hs
        · exact absurd hargs.symm (by simp)
      · intro h
        generalize hu : (Term.app 1 [] : Term Nat Nat) = u at h
        change CStepE rootOnly (relConv (CStepLevel rootOnly n)) w u at h
        cases h with
        | root hr =>
            obtain ⟨crule, hmem, σ, -, ht, -⟩ := hr
            simp only [rootOnly, List.mem_singleton] at hmem
            subst hmem
            rw [← hu] at ht
            simp at ht
        | arg g pre post _ =>
            simp at hu

/-- **A root step between terms of the same argument shape does not project.** `F(c)` rewrites to
`F(d)` at level `1`, but `c` and `d` are not convertible. -/
theorem root_history_projection_fails :
    Nonempty (TraceData (SignedData (LevelStepData rootOnly 1))
      (.app 0 ([] ++ Term.app 1 [] :: [])) (.app 0 ([] ++ Term.app 2 [] :: []))) ∧
      ¬ cconv rootOnly (.app 1 []) (.app 2 []) := by
  refine ⟨⟨TraceData.snoc TraceData.nil (SignedData.forward
    (ContextStepData.root ⟨_, List.Mem.head _, Subst.id, rfl, rfl, fun i => Fin.elim0 i⟩))⟩, ?_⟩
  intro h
  rcases Relation.ReflTransGen.cases_head h with he | ⟨w, hw, -⟩
  · simp at he
  · rcases hw with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact (rootOnly_c_isolated m w).1 hm
    · exact (rootOnly_c_isolated m w).2 hm

end Projection

end OperatorKO7.Meta.UniqueNormalization.ConditionHistory
