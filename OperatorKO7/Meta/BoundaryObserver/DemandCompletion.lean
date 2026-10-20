import OperatorKO7.Meta.BoundaryObserver.DemandTransport
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

set_option autoImplicit false

/-!
# Finite constraints, closed languages and conservative self-extension

Graph: notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md, M4.1-M4.5.
The completion theorem uses compact witnesses and closed acceptance sets.
Finite agreement characterizes closure on the actual, identity-observed input carrier.
A fresh code represents the old changed diagonal, not the enlarged diagonal.
-/

namespace UniversalObservation.Completion

open Demand Transport Set

universe u v

/-- Compact witnesses turn every finite successful restriction into one global witness. -/
theorem compact_completion_iff {I W : Type*} [TopologicalSpace W] [CompactSpace W]
    (P : Problem I W) (hclosed : ∀ i, IsClosed {w | P.sat w i}) :
    (∀ D : Finset I, Good P (D : Set I)) ↔ Good P Set.univ := by
  constructor
  · intro h
    have hf : ∀ D : Finset I, (⋂ i ∈ D, {w | P.sat w i}).Nonempty := by
      intro D
      obtain ⟨w, hw⟩ := h D
      exact ⟨w, by simpa only [mem_iInter, mem_setOf_eq] using hw⟩
    obtain ⟨w, hw⟩ := CompactSpace.iInter_nonempty hclosed hf
    exact ⟨w, fun i _ => Set.mem_iInter.mp hw i⟩
  · intro h D
    exact good_downward P (Set.subset_univ _) h

/-- Global failure in a compact closed model has a finite minimal certificate. -/
theorem compact_failure_has_finite_obstruction {I W : Type*}
    [TopologicalSpace W] [CompactSpace W] (P : Problem I W)
    (hclosed : ∀ i, IsClosed {w | P.sat w i}) (hbad : ¬ Good P Set.univ) :
    ∃ B : Finset I, MinimalBad P B := by
  classical
  have hn : ¬ ∀ D : Finset I, Good P (D : Set I) :=
    fun h => hbad ((compact_completion_iff P hclosed).mp h)
  push_neg at hn
  obtain ⟨D, hD⟩ := hn
  obtain ⟨B, _, hB⟩ := exists_minimal_bad P D hD
  exact ⟨B, hB⟩

/-- Natural threshold witnesses pass each finite set but no global set. -/
def thresholdProblem : Problem ℕ ℕ where
  sat w i := i ≤ w

theorem threshold_finite_good (D : Finset ℕ) : Good thresholdProblem (D : Set ℕ) := by
  refine ⟨D.sup id, ?_⟩
  intro i hi
  exact Finset.le_sup (f := id) hi

theorem threshold_global_bad : ¬ Good thresholdProblem Set.univ := by
  rintro ⟨w, hw⟩
  exact Nat.not_succ_le_self w (hw (w + 1) (Set.mem_univ _))

theorem threshold_no_finite_obstruction (B : Finset ℕ) : ¬ MinimalBad thresholdProblem B :=
  fun h => h.1 (threshold_finite_good B)

/-- Finite agreement is the actual product-topology closure criterion for discrete outputs. -/
theorem mem_closure_iff_finite_agreement {Y V : Type*}
    [TopologicalSpace V] [DiscreteTopology V] (F : Set (Y → V)) (T : Y → V) :
    T ∈ closure F ↔ ∀ D : Finset Y, ∃ f ∈ F, ∀ y ∈ D, f y = T y := by
  classical
  constructor
  · intro h D
    have hopen : IsOpen (⋂ y ∈ D, {f : Y → V | f y = T y}) := by
      apply isOpen_biInter_finset
      intro y _
      exact (isOpen_discrete ({T y} : Set V)).preimage
        (show Continuous (fun f : Y → V => f y) from continuous_apply y)
    have hT : T ∈ ⋂ y ∈ D, {f : Y → V | f y = T y} := by simp
    obtain ⟨f, hfD, hfF⟩ := mem_closure_iff.mp h _ hopen hT
    exact ⟨f, hfF, by simpa only [mem_iInter, mem_setOf_eq] using hfD⟩
  · intro h
    apply mem_closure_iff.mpr
    intro U hU hTU
    obtain ⟨D, opens, hopen, hsub⟩ := isOpen_pi_iff.mp hU T hTU
    obtain ⟨f, hfF, hfD⟩ := h D
    refine ⟨f, hsub ?_, hfF⟩
    intro y hy
    rw [hfD y hy]
    exact (hopen y hy).2

/-- No finite output-cardinality assumption is needed for this closure characterization. -/
theorem closed_readouts_iff {Y V : Type*} [TopologicalSpace V] [DiscreteTopology V]
    (F : Set (Y → V)) :
    IsClosed F ↔ ∀ T : Y → V,
      (∀ D : Finset Y, ∃ f ∈ F, ∀ y ∈ D, f y = T y) → T ∈ F := by
  rw [← closure_subset_iff_isClosed]
  constructor
  · intro h T hT
    exact h ((mem_closure_iff_finite_agreement F T).mpr hT)
  · intro h T hT
    exact h T ((mem_closure_iff_finite_agreement F T).mp hT)

/-- Nonclosed languages have a target with finite success and no permitted global readout. -/
theorem nonclosed_readouts_have_missing_limit {Y V : Type*}
    [TopologicalSpace V] [DiscreteTopology V] (F : Set (Y → V)) (h : ¬ IsClosed F) :
    ∃ T : Y → V, T ∉ F ∧ ∀ D : Finset Y, ∃ f ∈ F, ∀ y ∈ D, f y = T y := by
  classical
  rw [closed_readouts_iff] at h
  push_neg at h
  obtain ⟨T, hT, hn⟩ := h
  exact ⟨T, hn, hT⟩

/-- Closure is only needed on the attained reports, not on unused output codes. -/
def attainedReadouts {X Y V : Type*} (O : X → Y) (F : Set (Y → V)) :
    Set ((Set.range O) → V) := {g | ∃ f ∈ F, ∀ y : Set.range O, g y = f y.val}

theorem attained_readout_global_iff {X Y V : Type*} (O : X → Y) (T : X → V)
    (F : Set (Y → V)) :
    Good (readoutProblem O T F) Set.univ ↔
      ∃ g ∈ attainedReadouts O F, ∀ x, g ⟨O x, Set.mem_range_self x⟩ = T x := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun y => f.val y.val, ⟨f.val, f.property, fun _ => rfl⟩, ?_⟩
    exact fun x => hf x (Set.mem_univ x)
  · rintro ⟨g, ⟨f, hf, hg⟩, hT⟩
    refine ⟨⟨f, hf⟩, ?_⟩
    intro x _
    exact (hg ⟨O x, Set.mem_range_self x⟩).symm.trans (hT x)

/-- Identity of unused reports is not a demand on the observed source. -/
theorem unused_report_control :
    (∀ _ : Unit, (fun _ : Bool => false) false = (fun b : Bool => b) false) ∧
      (fun _ : Bool => false) ≠ (fun b : Bool => b) := by
  constructor
  · intro _; rfl
  · intro h
    have he := congrFun h true
    cases he

/-- One new code evaluates the old transformed diagonal on the old inputs. -/
def extendEval {C V : Type*} (E : C → C → V) (j : V → V) (v0 : V) :
    Option C → Option C → V
  | some c, some x => E c x
  | none, some x => j (E x x)
  | _, none => v0

theorem extend_old_table {C V : Type*} (E : C → C → V) (j : V → V)
    (v0 : V) (c x : C) : extendEval E j v0 (some c) (some x) = E c x := rfl

theorem extend_old_diagonal {C V : Type*} (E : C → C → V) (j : V → V)
    (v0 : V) (x : C) : extendEval E j v0 none (some x) = j (E x x) := rfl

/-- The fixed-point-free target-changing operation excludes its own diagonal code. -/
theorem transformed_diagonal_absent {C V : Type*} (E : C → C → V)
    (j : V → V) (noFix : ∀ v, j v ≠ v) :
    ¬ ∃ c, ∀ x, E c x = j (E x x) := by
  rintro ⟨c, hc⟩
  exact noFix (E c c) (hc c).symm

theorem conservative_diagonal_extension {C V : Type*} (E : C → C → V)
    (j : V → V) (v0 : V) (noFix : ∀ v, j v ≠ v) :
    (∀ c x, extendEval E j v0 (some c) (some x) = E c x) ∧
    (∀ x, extendEval E j v0 none (some x) = j (E x x)) ∧
    ¬ ∃ c, ∀ x, extendEval E j v0 c x = j (extendEval E j v0 x x) := by
  exact ⟨fun _ _ => rfl, fun _ => rfl, transformed_diagonal_absent (extendEval E j v0) j noFix⟩

def diagonalProblem {C V : Type*} (E : C → C → V) (j : V → V) : Problem C C where
  sat c x := E c x = j (E x x)

def extendedOldProblem {C V : Type*} (E : C → C → V) (j : V → V) (v0 : V) :
    Problem C (Option C) where
  sat c x := extendEval E j v0 c (some x) = j (E x x)

def diagonalEmbedding {C V : Type*} (E : C → C → V) (j : V → V) (v0 : V) :
    ConservativeEmbedding (diagonalProblem E j) (extendedOldProblem E j v0) where
  demands := Function.Embedding.refl C
  witnesses := ⟨Option.some, Option.some_injective C⟩
  old_satisfaction _ _ := Iff.rfl

theorem old_diagonal_resolved {C V : Type*} (E : C → C → V) (j : V → V) (v0 : V) :
    Good (extendedOldProblem E j v0) Set.univ := ⟨none, fun _ _ => rfl⟩

theorem diagonal_extension_no_reimport {C V : Type*} (E : C → C → V)
    (j : V → V) (v0 : V) (noFix : ∀ v, j v ≠ v) :
    ¬ Reimport (diagonalProblem E j) (extendedOldProblem E j v0) id Set.univ := by
  apply no_reimport_of_new_solution
  · rintro ⟨c, hc⟩
    exact transformed_diagonal_absent E j noFix ⟨c, fun x => hc x (Set.mem_univ x)⟩
  · simpa using old_diagonal_resolved E j v0

/-- A stage adds one code, with its entire preceding table retained. -/
def Stage (C : Type u) : ℕ → Type u
  | 0 => C
  | n + 1 => Option (Stage C n)

def stageEval {C : Type u} {V : Type v} (E : C → C → V) (j : V → V) (v0 : V) :
    (n : ℕ) → Stage C n → Stage C n → V
  | 0 => E
  | n + 1 => extendEval (stageEval E j v0 n) j v0

def stageInclude {C : Type u} (n : ℕ) : (k : ℕ) → Stage C n → Stage C (n + k)
  | 0, c => c
  | k + 1, c => some (stageInclude n k c)

theorem stageInclude_injective {C : Type u} (n k : ℕ) :
    Function.Injective (stageInclude (C := C) n k) := by
  induction k with
  | zero => exact Function.injective_id
  | succ k ih =>
    intro a b h
    exact ih (Option.some.inj h)

theorem stage_table_preserved {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n k : ℕ) (c x : Stage C n) :
    stageEval E j v0 (n + k) (stageInclude n k c) (stageInclude n k x) =
      stageEval E j v0 n c x := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

theorem stage_old_diagonal_represented {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n : ℕ) (x : Stage C n) :
    stageEval E j v0 (n + 1) none (some x) = j (stageEval E j v0 n x x) := rfl

theorem every_stage_diagonal_absent {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (noFix : ∀ v, j v ≠ v) (n : ℕ) :
    ¬ ∃ c, ∀ x, stageEval E j v0 n c x = j (stageEval E j v0 n x x) :=
  transformed_diagonal_absent (stageEval E j v0 n) j noFix

instance stageFintype (C : Type u) [Fintype C] (n : ℕ) : Fintype (Stage C n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype C)
  | succ n ih =>
    letI : Fintype (Stage C n) := ih
    exact inferInstanceAs (Fintype (Option (Stage C n)))

/-- The finite extension gains one code per stage, not one independent bit per stage. -/
theorem stage_cardinality {C : Type u} [Fintype C] (n : ℕ) :
    Nat.card (Stage C n) = Fintype.card C + n := by
  induction n with
  | zero => simp [Stage]
  | succ n ih =>
    change Nat.card (Option (Stage C n)) = Fintype.card C + (n + 1)
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    have hi : Fintype.card (Stage C n) = Fintype.card C + n := by simpa using ih
    omega

/-- A budget stop has no implicit truth field. -/
inductive Certificate {I W : Type*} (P : Problem I W) (D : Set I)
  | witness (w : W) (valid : w ∈ Witnesses P D)
  | obstruction (proof : ¬ Good P D)
  | resourceHalt (budget : ℕ)

theorem witness_excludes_obstruction {I W : Type*} (P : Problem I W) (D : Set I)
    (w : W) (hw : w ∈ Witnesses P D) : ¬ (¬ Good P D) := fun h => h ⟨w, hw⟩

theorem resource_halt_has_both_source_statuses (budget : ℕ) :
    Nonempty (Certificate (⟨fun _ _ => True⟩ : Problem Unit Unit) Set.univ) ∧
    Nonempty (Certificate (⟨fun _ _ => False⟩ : Problem Unit Unit) Set.univ) ∧
    Good (⟨fun _ _ => True⟩ : Problem Unit Unit) Set.univ ∧
    ¬ Good (⟨fun _ _ => False⟩ : Problem Unit Unit) Set.univ := by
  refine ⟨⟨.resourceHalt budget⟩, ⟨.resourceHalt budget⟩, ⟨(), fun _ _ => trivial⟩, ?_⟩
  rintro ⟨w, hw⟩
  exact hw () (Set.mem_univ ())


/-- One source process determines all demands, licenses and resource coordinates. -/
structure SourceContract where
  Process : Type
  Input : Type
  Output : Type
  Witness : Type
  source : Process
  evaluate : Process → Input → Output
  interpret : Witness → Process
  allowed : (k : ℕ) → Set (Input → Fin k)
  combines : Set Input → (k : ℕ) → (Input → Fin k) → Prop
  assemble : (k : ℕ) → (Input → Fin k) → (Fin k → Witness) → Process
  cost : Process → ℕ → ℝ

def SourceContract.problem (C : SourceContract) : Problem C.Input C.Witness where
  sat w i := C.evaluate (C.interpret w) i = C.evaluate C.source i

def SourceContract.nativeProblem (C : SourceContract) : Problem C.Input C.Process where
  sat p i := C.evaluate p i = C.evaluate C.source i

def SourceContract.menu (C : SourceContract) : RepairMenu C.Input C.Witness C.problem where
  allowed := C.allowed
  combines := C.combines

def SourceContract.combinerLaw (C : SourceContract) : Prop :=
  CombinerSound C.problem C.menu C.nativeProblem C.assemble

/-- Every licensed combination satisfies its own source equation. -/
theorem assembled_source_correct (C : SourceContract) (hlaw : C.combinerLaw)
    (D : Set C.Input) (k : ℕ) (s : C.Input → Fin k) (ws : Fin k → C.Witness)
    (ha : s ∈ C.allowed k) (hc : C.combines D k s)
    (hw : ∀ i ∈ D, C.problem.sat (ws (s i)) i) :
    ∀ i ∈ D, C.evaluate (C.assemble k s ws) i = C.evaluate C.source i :=
  hlaw D k s ws ha hc hw

/-- The realized process is assembled from the actual selected witnesses. -/
theorem source_repair_realized (C : SourceContract) (hlaw : C.combinerLaw)
    (D : Set C.Input) (k : ℕ) (h : RepairFeasible C.problem C.menu D k) :
    ∃ (s : C.Input → Fin k) (ws : Fin k → C.Witness),
      s ∈ C.allowed k ∧ C.combines D k s ∧
      (∀ i ∈ D, C.problem.sat (ws (s i)) i) ∧
      (∀ i ∈ D, C.evaluate (C.assemble k s ws) i = C.evaluate C.source i) := by
  obtain ⟨s, ha, hc, ws, hw⟩ := h
  exact ⟨s, ws, ha, hc, hw, assembled_source_correct C hlaw D k s ws ha hc hw⟩

/-- The changed diagonal uses this source and its interpreted candidate processes. -/
theorem source_diagonal_exclusion (C : SourceContract) (e : C.Witness ≃ C.Input)
    (j : C.Output → C.Output) (noFix : ∀ v, j v ≠ v)
    (htarget : ∀ w, C.evaluate C.source (e w) = j (C.evaluate (C.interpret w) (e w))) :
    ¬ Good C.problem Set.univ := by
  rintro ⟨w, hw⟩
  have h := hw (e w) (Set.mem_univ _)
  change C.evaluate (C.interpret w) (e w) = C.evaluate C.source (e w) at h
  rw [htarget w] at h
  exact noFix _ h.symm

/-- Source-indexed finite, licensed, compact, cost and diagonal conclusions. -/
def CoreGoal (C : SourceContract) : Prop :=
  (∀ D : Finset C.Input,
    ¬ Good C.problem (D : Set C.Input) ↔
      ∃ B : Finset C.Input, B ⊆ D ∧ MinimalBad C.problem B) ∧
  (∀ [Fintype C.Input] [Nonempty C.Witness] (D : Set C.Input) (k : ℕ), 0 < k →
    (RepairFeasible C.problem C.menu D k ↔
      ∃ s ∈ C.allowed k, C.combines D k s ∧ ColorsOn C.problem D k s)) ∧
  (C.combinerLaw → ∀ D k, RepairFeasible C.problem C.menu D k → Good C.nativeProblem D) ∧
  (∀ [TopologicalSpace C.Witness] [CompactSpace C.Witness],
    (∀ i, IsClosed {w | C.problem.sat w i}) →
    ((∀ D : Finset C.Input, Good C.problem (D : Set C.Input)) ↔ Good C.problem Set.univ)) ∧
  (∀ (J V : Type) (Q : Problem J V) (e : DemandIso C.problem Q)
    (cost : V → ℕ → ℝ),
    (∀ w j, cost (e.witnesses w) j = C.cost (C.interpret w) j) → ∀ D budget,
    (BudgetFeasible C.problem D (fun w => C.cost (C.interpret w)) budget ↔
      BudgetFeasible Q (e.demands '' D) cost budget)) ∧
  (∀ (e : C.Witness ≃ C.Input) (j : C.Output → C.Output),
    (∀ v, j v ≠ v) →
    (∀ w, C.evaluate C.source (e w) = j (C.evaluate (C.interpret w) (e w))) →
    ¬ Good C.problem Set.univ)

/-- All conclusions are derived from the one retained source contract. -/
theorem source_observation_repair_core (C : SourceContract) : CoreGoal C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finite_obstruction_iff C.problem
  · intro _ _ D k _
    exact licensed_coloring_iff C.problem C.menu D k
  · exact source_repair_sound C.problem C.menu C.nativeProblem C.assemble
  · intro _ _ hclosed
    exact compact_completion_iff C.problem hclosed
  · intro J V Q e cost hcost D budget
    exact (budget_transport_iff e (fun w => C.cost (C.interpret w)) cost hcost D budget).symm
  · exact source_diagonal_exclusion C

/-- A readout source retains the original target and its actual selected extension. -/
def readoutSource (X Y V : Type) (O : X → Y) (T : X → V)
    (F : Set (Y → V)) (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set X → (k : ℕ) → (X → Fin k) → Prop)
    (cost : (X → V) → ℕ → ℝ) : SourceContract where
  Process := X → V
  Input := X
  Output := V
  Witness := F
  source := T
  evaluate p x := p x
  interpret f x := f.val (O x)
  allowed := allowed
  combines := combines
  assemble _ s ws x := (ws (s x)).val (O x)
  cost := cost

theorem readoutSource_problem (X Y V : Type) (O : X → Y) (T : X → V)
    (F : Set (Y → V)) (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set X → (k : ℕ) → (X → Fin k) → Prop)
    (cost : (X → V) → ℕ → ℝ) :
    (readoutSource X Y V O T F allowed combines cost).problem = readoutProblem O T F := rfl

theorem readoutSource_combiner (X Y V : Type) (O : X → Y) (T : X → V)
    (F : Set (Y → V)) (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set X → (k : ℕ) → (X → Fin k) → Prop)
    (cost : (X → V) → ℕ → ℝ) :
    (readoutSource X Y V O T F allowed combines cost).combinerLaw := by
  intro D k s ws _ _ hw
  exact hw

theorem readoutSource_core (X Y V : Type) (O : X → Y) (T : X → V)
    (F : Set (Y → V)) (allowed : (k : ℕ) → Set (X → Fin k))
    (combines : Set X → (k : ℕ) → (X → Fin k) → Prop)
    (cost : (X → V) → ℕ → ℝ) :
    CoreGoal (readoutSource X Y V O T F allowed combines cost) :=
  source_observation_repair_core _

/-! ## The directed union retains every finite-stage evaluation -/

/-- The n-th added code has the natural tag n; original codes retain their own tag. -/
def stageEncode {C : Type u} : (n : ℕ) → Stage C n → Sum C ℕ
  | 0, c => Sum.inl c
  | n + 1, none => Sum.inr n
  | n + 1, some c => stageEncode n c

/-- A code present at stage n has an added-code tag strictly less than n. -/
theorem stageEncode_tag_lt {C : Type u} (n : ℕ) (c : Stage C n) (m : ℕ)
    (h : stageEncode n c = Sum.inr m) : m < n := by
  induction n with
  | zero => cases h
  | succ n ih =>
    cases c with
    | none =>
      have hm : n = m := Sum.inr.inj h
      omega
    | some c => exact Nat.lt_trans (ih c h) (Nat.lt_succ_self n)

/-- Distinct finite-stage codes remain distinct in the directed-union carrier. -/
theorem stageEncode_injective {C : Type u} (n : ℕ) :
    Function.Injective (stageEncode (C := C) n) := by
  induction n with
  | zero => exact Sum.inl_injective
  | succ n ih =>
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        exact False.elim (Nat.lt_irrefl n (stageEncode_tag_lt n b n h.symm))
    | some a =>
      cases b with
      | none =>
        exact False.elim (Nat.lt_irrefl n (stageEncode_tag_lt n a n h))
      | some b => exact congrArg some (ih h)

/-- Every later embedding gives exactly the same union code. -/
theorem stageEncode_include {C : Type u} (n k : ℕ) (c : Stage C n) :
    stageEncode (n + k) (stageInclude n k c) = stageEncode n c := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- Every union code occurs at a specific finite stage. -/
theorem stageEncode_jointly_surjective {C : Type u} :
    Function.Surjective (fun c : Sigma (Stage C) => stageEncode c.1 c.2) := by
  intro c
  cases c with
  | inl c => exact ⟨⟨0, c⟩, rfl⟩
  | inr n => exact ⟨⟨n + 1, none⟩, rfl⟩

/-- The union table is an actual evaluator on original codes and all added codes. -/
def limitEval {C : Type u} {V : Type v} (E : C → C → V) (j : V → V) (v0 : V) :
    Sum C ℕ → Sum C ℕ → V
  | .inl c, .inl x => E c x
  | .inl _, .inr _ => v0
  | .inr _, .inl x => j (E x x)
  | .inr n, .inr m => if m < n then j v0 else v0

/-- An added code evaluated at itself keeps its declared new-input value. -/
theorem limitEval_added_diagonal {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n : ℕ) :
    limitEval E j v0 (.inr n) (.inr n) = v0 := by
  simp [limitEval]

/-- The diagonal of every finite table agrees with the union table. -/
theorem stage_diagonal_eq_limit {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n : ℕ) (c : Stage C n) :
    stageEval E j v0 n c c =
      limitEval E j v0 (stageEncode n c) (stageEncode n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases c with
    | none => simp [stageEval, extendEval, stageEncode, limitEval]
    | some c => exact ih c

/-- The next new row agrees with the changed diagonal on every old input. -/
theorem limitEval_new_row {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n : ℕ) (c : Stage C n) :
    limitEval E j v0 (.inr n) (stageEncode n c) =
      j (limitEval E j v0 (stageEncode n c) (stageEncode n c)) := by
  cases he : stageEncode n c with
  | inl c => rfl
  | inr m =>
    have hm : m < n := stageEncode_tag_lt n c m he
    simp [limitEval, hm]

/-- A new input column keeps its declared value on every preceding row. -/
theorem limitEval_new_column {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n : ℕ) (c : Stage C n) :
    limitEval E j v0 (stageEncode n c) (.inr n) = v0 := by
  cases he : stageEncode n c with
  | inl c => rfl
  | inr m =>
    have hm : m < n := stageEncode_tag_lt n c m he
    simp [limitEval, Nat.not_lt_of_ge hm.le]

/-- The union table preserves every entry at every finite stage. -/
theorem stage_eval_eq_limit {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n : ℕ) (c x : Stage C n) :
    stageEval E j v0 n c x =
      limitEval E j v0 (stageEncode n c) (stageEncode n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases c with
    | none =>
      cases x with
      | none => simp [stageEval, extendEval, stageEncode, limitEval]
      | some x =>
        change j (stageEval E j v0 n x x) = limitEval E j v0 (.inr n) (stageEncode n x)
        rw [stage_diagonal_eq_limit, limitEval_new_row]
    | some c =>
      cases x with
      | none => exact (limitEval_new_column E j v0 n c).symm
      | some x => exact ih c x

/-- Two stage presentations of the same source/input pair yield the same answer. -/
theorem stage_eval_independent_of_representatives {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (n m : ℕ)
    (c x : Stage C n) (d y : Stage C m)
    (hc : stageEncode n c = stageEncode m d) (hx : stageEncode n x = stageEncode m y) :
    stageEval E j v0 n c x = stageEval E j v0 m d y := by
  rw [stage_eval_eq_limit, stage_eval_eq_limit, hc, hx]

/-- Even the union of all finite extensions misses its own newly specified diagonal. -/
theorem limit_diagonal_absent {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (noFix : ∀ v, j v ≠ v) :
    ¬ ∃ c, ∀ x, limitEval E j v0 c x = j (limitEval E j v0 x x) :=
  transformed_diagonal_absent (limitEval E j v0) j noFix

/-- The one-code extension does not preserve closure under an operation moving v0. -/
theorem extend_not_closed_under_change {C : Type u} {V : Type v}
    (E : C → C → V) (j : V → V) (v0 : V) (hmove : j v0 ≠ v0) :
    ¬ ∃ changeCode : Option C → Option C,
      ∀ c x, extendEval E j v0 (changeCode c) x = j (extendEval E j v0 c x) := by
  rintro ⟨changeCode, hc⟩
  have h := hc none none
  have he : extendEval E j v0 (changeCode none) none = v0 := by
    cases changeCode none <;> rfl
  rw [he] at h
  exact hmove h.symm


/-! ## M4.5: finite retained coloring on arbitrary source carriers -/

/-- A finite retained set suffices for the selector and obstruction equivalence. -/
theorem selectedOn_iff_colorsOn_finset {I : Type u} {W : Type v}
    (P : Problem I W) (D : Finset I) (k : ℕ) (s : I → Fin k) :
    SelectedOn P (D : Set I) k s ↔ ColorsOn P (D : Set I) k s := by
  classical
  constructor
  · rintro ⟨xs, hx⟩ B hBD hB ⟨j, hj⟩
    apply hB.1
    refine ⟨xs j, ?_⟩
    intro i hi
    rw [← hj i hi]
    exact hx i (hBD hi)
  · intro hc
    have hgood (j : Fin k) :
        Good P ((D.filter (fun i => s i = j) : Finset I) : Set I) := by
      by_contra hn
      obtain ⟨B, hBE, hB⟩ :=
        (finite_obstruction_iff P (D.filter (fun i => s i = j))).mp hn
      have hb (i : I) (hi : i ∈ B) : i ∈ D ∧ s i = j :=
        Finset.mem_filter.mp (hBE hi)
      exact hc B (fun i hi => (hb i hi).1) hB ⟨j, fun i hi => (hb i hi).2⟩
    refine ⟨fun j => Classical.choose (hgood j), ?_⟩
    intro i hi
    exact Classical.choose_spec (hgood (s i)) i (Finset.mem_filter.mpr ⟨hi, rfl⟩)

/-- The retained-set form keeps the original global selector domain. -/
theorem selectedOn_iff_colorsOn_finite {I : Type u} {W : Type v}
    (P : Problem I W) (D : Set I) (hD : D.Finite) (k : ℕ) (s : I → Fin k) :
    SelectedOn P D k s ↔ ColorsOn P D k s := by
  simpa only [hD.coe_toFinset] using selectedOn_iff_colorsOn_finset P hD.toFinset k s

/-- Both source permissions remain unchanged under finite retained coloring. -/
theorem licensed_coloring_iff_finite {I : Type u} {W : Type v}
    (P : Problem I W) (menu : RepairMenu I W P) (D : Set I) (hD : D.Finite) (k : ℕ) :
    RepairFeasible P menu D k ↔
      ∃ s ∈ menu.allowed k, menu.combines D k s ∧ ColorsOn P D k s := by
  constructor
  · rintro ⟨s, ha, hc, hw⟩
    exact ⟨s, ha, hc, (selectedOn_iff_colorsOn_finite P D hD k s).mp hw⟩
  · rintro ⟨s, ha, hc, hw⟩
    exact ⟨s, ha, hc, (selectedOn_iff_colorsOn_finite P D hD k s).mpr hw⟩

/-- The source Goal covers arbitrary witness carriers and every selector alphabet. -/
def FiniteRetainedColoringGoal (C : SourceContract) : Prop :=
  ∀ (D : Set C.Input), D.Finite → ∀ k : ℕ,
    RepairFeasible C.problem C.menu D k ↔
      ∃ s ∈ C.allowed k, C.combines D k s ∧ ColorsOn C.problem D k s

theorem finiteRetainedColoringGoal (C : SourceContract) : FiniteRetainedColoringGoal C := by
  intro D hD k
  exact licensed_coloring_iff_finite C.problem C.menu D hD k

/-- The original threshold evaluator has global finite-obstruction coloring without selection. -/
theorem threshold_global_coloring_not_selection :
    ColorsOn thresholdProblem Set.univ 1 (fun _ => 0) ∧
      ¬ SelectedOn thresholdProblem Set.univ 1 (fun _ => 0) := by
  constructor
  · intro B _ hB
    exact False.elim (threshold_no_finite_obstruction B hB)
  · rintro ⟨xs, hx⟩
    exact threshold_global_bad ⟨xs 0, hx⟩

/-- The empty source supplies the zero-color endpoint without an inhabited candidate carrier. -/
def emptyColorSource : SourceContract where
  Process := Unit
  Input := Empty
  Output := Unit
  Witness := Empty
  source := ()
  evaluate := fun _ _ => ()
  interpret := fun w => Empty.elim w
  allowed := fun _ => Set.univ
  combines := fun _ _ _ => True
  assemble := fun _ _ _ => ()
  cost := fun _ _ => 0

theorem empty_zero_coloring_scope :
    ¬ Nonempty emptyColorSource.Witness ∧
      RepairFeasible emptyColorSource.problem emptyColorSource.menu Set.univ 0 := by
  constructor
  · rintro ⟨w⟩
    cases w
  · refine ⟨(fun i => Empty.elim i), Set.mem_univ _, trivial,
      (fun j => Fin.elim0 j), ?_⟩
    intro i _
    cases i

end UniversalObservation.Completion
