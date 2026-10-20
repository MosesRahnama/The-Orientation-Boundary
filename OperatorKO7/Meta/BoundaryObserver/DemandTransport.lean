import OperatorKO7.Meta.BoundaryObserver.DemandComplex
import OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation
import OperatorKO7.Meta.BoundaryObserver.ObserverRealization
import OperatorKO7.Meta.BoundaryObserver.ObservationTransport
import OperatorKO7.Meta.BoundaryObserver.InstrumentComposition

set_option autoImplicit false

/-!
# Source-bound transport of demands and permitted witnesses

Graph: `notes/universal-roadmap/UNIVERSAL-OBSERVATION-PROOF-GRAPH.md`, M2.1-M2.5.
All inverse statements use witness and demand equivalences with an incidence law.
A conservative embedding alone does not return new proofs to the old language.
Adaptive instances retain the actual experiments and executed traces.
-/

namespace UniversalObservation.Transport

open Demand

structure DemandIso {I J W V : Type*} (P : Problem I W) (Q : Problem J V) where
  demands : I ≃ J
  witnesses : W ≃ V
  satisfaction : ∀ w i, Q.sat (witnesses w) (demands i) ↔ P.sat w i

namespace DemandIso

variable {I J K W V U : Type*} {P : Problem I W} {Q : Problem J V} {R : Problem K U}

def refl (P : Problem I W) : DemandIso P P where
  demands := Equiv.refl I
  witnesses := Equiv.refl W
  satisfaction _ _ := Iff.rfl

def symm (e : DemandIso P Q) : DemandIso Q P where
  demands := e.demands.symm
  witnesses := e.witnesses.symm
  satisfaction v j := by
    simpa using (e.satisfaction (e.witnesses.symm v) (e.demands.symm j)).symm

def trans (e : DemandIso P Q) (f : DemandIso Q R) : DemandIso P R where
  demands := e.demands.trans f.demands
  witnesses := e.witnesses.trans f.witnesses
  satisfaction w i := (f.satisfaction (e.witnesses w) (e.demands i)).trans (e.satisfaction w i)

theorem witness_iff (e : DemandIso P Q) (D : Set I) (w : W) :
    e.witnesses w ∈ Witnesses Q (e.demands '' D) ↔ w ∈ Witnesses P D := by
  constructor
  · intro h i hi
    exact (e.satisfaction w i).mp (h (e.demands i) ⟨i, hi, rfl⟩)
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact (e.satisfaction w i).mpr (h i hi)

def witnessEquiv (e : DemandIso P Q) (D : Set I) :
    Witnesses P D ≃ Witnesses Q (e.demands '' D) where
  toFun w := ⟨e.witnesses w.val, (e.witness_iff D w.val).mpr w.property⟩
  invFun v := ⟨e.witnesses.symm v.val, (e.witness_iff D _).mp (by rw [e.witnesses.apply_symm_apply]; exact v.property)⟩
  left_inv w := Subtype.ext (e.witnesses.symm_apply_apply w.val)
  right_inv v := Subtype.ext (e.witnesses.apply_symm_apply v.val)

theorem good_transport (e : DemandIso P Q) (D : Set I) :
    Good Q (e.demands '' D) ↔ Good P D := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨e.witnesses.symm v, (e.witness_iff D _).mp (by simpa using hv)⟩
  · rintro ⟨w, hw⟩
    exact ⟨e.witnesses w, (e.witness_iff D w).mpr hw⟩

theorem minimal_map (e : DemandIso P Q) (B : Finset I) (hB : MinimalBad P B) :
    MinimalBad Q (B.map e.demands.toEmbedding) := by
  classical
  have hg (A : Finset I) : Good Q (A.map e.demands.toEmbedding : Set J) ↔ Good P (A : Set I) := by
    simpa only [Finset.coe_map] using e.good_transport (A : Set I)
  refine ⟨fun h => hB.1 ((hg B).mp h), ?_⟩
  intro A hA
  have hb : A.map e.demands.symm.toEmbedding ⊂ B := by
    have h := (Finset.map_ssubset_map (f := e.demands.symm.toEmbedding)).mpr hA
    simpa [Finset.map_map] using h
  have h := (hg (A.map e.demands.symm.toEmbedding)).mpr (hB.2 _ hb)
  simpa [Finset.map_map] using h

theorem minimal_transport_iff (e : DemandIso P Q) (B : Finset I) :
    MinimalBad Q (B.map e.demands.toEmbedding) ↔ MinimalBad P B := by
  constructor
  · intro h
    have hb := e.symm.minimal_map _ h
    simpa [symm, Finset.map_map] using hb
  · exact e.minimal_map B

def selector (e : DemandIso P Q) {k : ℕ} (s : I → Fin k) : J → Fin k :=
  fun j => s (e.demands.symm j)

theorem selector_inverse (e : DemandIso P Q) {k : ℕ} (s : I → Fin k) :
    e.symm.selector (e.selector s) = s := by
  funext i
  simp [selector, symm]

theorem selectedOn_transport_iff (e : DemandIso P Q) (D : Set I) (k : ℕ) (s : I → Fin k) :
    SelectedOn Q (e.demands '' D) k (e.selector s) ↔ SelectedOn P D k s := by
  constructor
  · rintro ⟨ws, hw⟩
    refine ⟨fun j => e.witnesses.symm (ws j), ?_⟩
    intro i hi
    apply (e.satisfaction _ i).mp
    simpa [selector] using hw (e.demands i) ⟨i, hi, rfl⟩
  · rintro ⟨ws, hw⟩
    refine ⟨fun j => e.witnesses (ws j), ?_⟩
    rintro j ⟨i, hi, rfl⟩
    simpa [selector] using (e.satisfaction _ i).mpr (hw i hi)

theorem colorsOn_transport_iff [Fintype I] [Fintype J]
    (e : DemandIso P Q) (D : Set I) (k : ℕ) (s : I → Fin k) :
    ColorsOn Q (e.demands '' D) k (e.selector s) ↔ ColorsOn P D k s := by
  rw [← selectedOn_iff_colorsOn, ← selectedOn_iff_colorsOn]
  exact e.selectedOn_transport_iff D k s

theorem selected_transport_iff (e : DemandIso P Q) (k : ℕ) (s : I → Fin k) :
    Selected Q k (e.selector s) ↔ Selected P k s := by
  simpa [SelectedOn, Selected] using e.selectedOn_transport_iff Set.univ k s

theorem selector_existence_transport (e : DemandIso P Q) (k : ℕ) :
    (∃ s : J → Fin k, Selected Q k s) ↔ ∃ s : I → Fin k, Selected P k s := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨e.symm.selector s, (e.symm.selected_transport_iff k s).mpr hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨e.selector s, (e.selected_transport_iff k s).mpr hs⟩

theorem minimumAlphabet_transport (e : DemandIso P Q) : minimumAlphabet Q = minimumAlphabet P := by
  unfold minimumAlphabet
  congr 1
  funext k
  exact propext (e.selector_existence_transport k)

/-- The permitted selectors and their source-specific combination licenses both commute. -/
structure MenuCorrespondence (e : DemandIso P Q) (p : RepairMenu I W P)
    (q : RepairMenu J V Q) : Prop where
  allowed : ∀ k s, e.selector s ∈ q.allowed k ↔ s ∈ p.allowed k
  combines : ∀ D k s, q.combines (e.demands '' D) k (e.selector s) ↔ p.combines D k s

theorem licensed_transport_iff (e : DemandIso P Q) (p : RepairMenu I W P)
    (q : RepairMenu J V Q) (hm : MenuCorrespondence e p q) (D : Set I) (k : ℕ) :
    RepairFeasible Q q (e.demands '' D) k ↔ RepairFeasible P p D k := by
  constructor
  · rintro ⟨s, hs, hc, hw⟩
    let t : I → Fin k := fun i => s (e.demands i)
    have he : e.selector t = s := by funext j; simp [selector, t]
    refine ⟨t, (hm.allowed k t).mp ?_, (hm.combines D k t).mp ?_,
      (e.selectedOn_transport_iff D k t).mp ?_⟩
    · simpa only [he] using hs
    · simpa only [he] using hc
    · simpa only [he] using hw
  · rintro ⟨s, hs, hc, hw⟩
    exact ⟨e.selector s, (hm.allowed k s).mpr hs, (hm.combines D k s).mpr hc,
      (e.selectedOn_transport_iff D k s).mpr hw⟩

end DemandIso

/-- Feasibility retains every cost coordinate, including incompatible physical units. -/
def BudgetFeasible {I W : Type*} (P : Problem I W) (D : Set I)
    (cost : W → ℕ → ℝ) (budget : ℕ → ℝ) : Prop :=
  ∃ w, w ∈ Witnesses P D ∧ ∀ j, cost w j ≤ budget j

theorem budget_transport_iff {I J W V : Type*} {P : Problem I W} {Q : Problem J V}
    (e : DemandIso P Q) (c : W → ℕ → ℝ) (d : V → ℕ → ℝ)
    (hc : ∀ w j, d (e.witnesses w) j = c w j) (D : Set I) (b : ℕ → ℝ) :
    BudgetFeasible Q (e.demands '' D) d b ↔ BudgetFeasible P D c b := by
  constructor
  · rintro ⟨v, hv, hb⟩
    refine ⟨e.witnesses.symm v, (e.witness_iff D _).mp (by simpa using hv), ?_⟩
    intro j
    simpa [← hc] using hb j
  · rintro ⟨w, hw, hb⟩
    exact ⟨e.witnesses w, (e.witness_iff D w).mpr hw, fun j => (hc w j).trans_le (hb j)⟩

theorem budget_mono {I W : Type*} (P : Problem I W) (D : Set I)
    (cost : W → ℕ → ℝ) {b c : ℕ → ℝ} (hbc : ∀ j, b j ≤ c j) :
    BudgetFeasible P D cost b → BudgetFeasible P D cost c := by
  rintro ⟨w, hw, hb⟩
  exact ⟨w, hw, fun j => (hb j).trans (hbc j)⟩

/-- A one-way source map gives one-way feasibility, with a stated monotone budget conversion. -/
theorem forward_budget_transport {I J W V B C : Type*} [Preorder B] [Preorder C]
    (P : Problem I W) (Q : Problem J V) (di : I → J) (wi : W → V)
    (hs : ∀ w i, P.sat w i → Q.sat (wi w) (di i))
    (cost : W → B) (cost' : V → C) (phi : B → C) (hp : Monotone phi)
    (hc : ∀ w, cost' (wi w) ≤ phi (cost w)) (D : Set I) (b : B) :
    (∃ w, w ∈ Witnesses P D ∧ cost w ≤ b) →
      ∃ v, v ∈ Witnesses Q (di '' D) ∧ cost' v ≤ phi b := by
  rintro ⟨w, hw, hb⟩
  refine ⟨wi w, ?_, (hc w).trans (hp hb)⟩
  rintro _ ⟨i, hi, rfl⟩
  exact hs w i (hw i hi)

structure ConservativeEmbedding {I J W V : Type*}
    (P : Problem I W) (Q : Problem J V) where
  demands : I ↪ J
  witnesses : W ↪ V
  old_satisfaction : ∀ w i, Q.sat (witnesses w) (demands i) ↔ P.sat w i

namespace ConservativeEmbedding

variable {I J K W V U : Type*} {P : Problem I W} {Q : Problem J V} {R : Problem K U}

def refl (P : Problem I W) : ConservativeEmbedding P P where
  demands := Function.Embedding.refl I
  witnesses := Function.Embedding.refl W
  old_satisfaction _ _ := Iff.rfl

def trans (e : ConservativeEmbedding P Q) (f : ConservativeEmbedding Q R) :
    ConservativeEmbedding P R where
  demands := e.demands.trans f.demands
  witnesses := e.witnesses.trans f.witnesses
  old_satisfaction w i := (f.old_satisfaction (e.witnesses w) (e.demands i)).trans (e.old_satisfaction w i)

theorem old_good_lifts (e : ConservativeEmbedding P Q) (D : Set I) :
    Good P D → Good Q (e.demands '' D) := by
  rintro ⟨w, hw⟩
  refine ⟨e.witnesses w, ?_⟩
  rintro _ ⟨i, hi, rfl⟩
  exact (e.old_satisfaction w i).mpr (hw i hi)

end ConservativeEmbedding

/-- New witnesses return only through an actual old-witness construction. -/
def Reimport {I J W V : Type*} (P : Problem I W) (Q : Problem J V)
    (e : I → J) (D : Set I) : Prop :=
  ∃ r : V → W, ∀ v, (∀ i ∈ D, Q.sat v (e i)) → ∀ i ∈ D, P.sat (r v) i

theorem reimport_good {I J W V : Type*} (P : Problem I W) (Q : Problem J V)
    (e : I → J) (D : Set I) (h : Reimport P Q e D) :
    Good Q (e '' D) → Good P D := by
  rintro ⟨v, hv⟩
  obtain ⟨r, hr⟩ := h
  exact ⟨r v, hr v (fun i hi => hv (e i) ⟨i, hi, rfl⟩)⟩

theorem no_reimport_of_new_solution {I J W V : Type*} (P : Problem I W) (Q : Problem J V)
    (e : I → J) (D : Set I) (hbad : ¬ Good P D) (hnew : Good Q (e '' D)) :
    ¬ Reimport P Q e D := fun hr => hbad (reimport_good P Q e D hr hnew)

/-- Independent tasks have distinct witness coordinates. -/
def productProblem {I J W V : Type*} (P : Problem I W) (Q : Problem J V) :
    Problem (Sum I J) (W × V) where
  sat w i := match i with
    | .inl x => P.sat w.1 x
    | .inr y => Q.sat w.2 y

theorem product_good_iff {I J W V : Type*} (P : Problem I W) (Q : Problem J V)
    (D : Set (Sum I J)) :
    Good (productProblem P Q) D ↔ Good P (Sum.inl ⁻¹' D) ∧ Good Q (Sum.inr ⁻¹' D) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨⟨w.1, fun i hi => hw (.inl i) hi⟩, ⟨w.2, fun j hj => hw (.inr j) hj⟩⟩
  · rintro ⟨⟨w, hw⟩, ⟨v, hv⟩⟩
    refine ⟨(w, v), ?_⟩
    intro i hi
    cases i with
    | inl i => exact hw i hi
    | inr j => exact hv j hi

theorem product_global_iff {I J W V : Type*} (P : Problem I W) (Q : Problem J V) :
    Good (productProblem P Q) Set.univ ↔ Good P Set.univ ∧ Good Q Set.univ := by
  simpa using product_good_iff P Q Set.univ

/-- A shared witness need not solve two tasks that each have a successful witness. -/
theorem shared_witness_control :
    (∃ b : Bool, b = false) ∧ (∃ b : Bool, b = true) ∧
      ¬ ∃ b : Bool, b = false ∧ b = true := by decide

/-- Equality of feasible demand sets does not supply an inverse map of witnesses. -/
theorem profile_not_witness_iso :
    (∀ D : Set Unit, Good (⟨fun _ _ => True⟩ : Problem Unit Unit) D ↔
      Good (⟨fun _ _ => True⟩ : Problem Unit Bool) D) ∧
      ¬ Nonempty (DemandIso (⟨fun _ _ => True⟩ : Problem Unit Unit)
        (⟨fun _ _ => True⟩ : Problem Unit Bool)) := by
  constructor
  · intro D
    exact ⟨fun _ => ⟨false, fun _ _ => trivial⟩, fun _ => ⟨(), fun _ _ => trivial⟩⟩
  · rintro ⟨e⟩
    have h : e.witnesses.symm false = e.witnesses.symm true := Subsingleton.elim _ _
    have he := e.witnesses.symm.injective h
    cases he

/-- The source demands are the actual positive-support input/output pairs. -/
def supportProblem {X Y V : Type*} (K : X → Y → ℝ) (T : X → V) :
    Problem {xy : X × Y // 0 < K xy.1 xy.2} (Y → V) where
  sat d xy := d xy.val.2 = T xy.val.1

theorem support_selector_iff {X Y V : Type*} (K : X → Y → ℝ) (T : X → V)
    (k : ℕ) (s : X → Fin k) :
    Selected (supportProblem K T) k (fun xy => s xy.val.1) ↔
      ∃ d : Y → Fin k → V, ∀ x y, 0 < K x y → d y (s x) = T x := by
  constructor
  · rintro ⟨ws, hw⟩
    exact ⟨fun y j => ws j y, fun x y h => hw ⟨(x, y), h⟩⟩
  · rintro ⟨d, hd⟩
    exact ⟨fun j y => d y j, fun xy => hd xy.val.1 xy.val.2 xy.property⟩

open OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation
open OperatorKO7.Meta.BoundaryObserver.ObservationTransport

/-- Witnesses are executable adaptive experiment trees, not arbitrary functions of all words. -/
def experimentProblem {X A Q V : Type*} (q : X → Q) (step : A → X → X)
    (target : X → V) : Problem X (Experiment A Q V) where
  sat test x := evaluate q step test x = target x

def experimentDemandIso {X Y A B Q R V W : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (value : V ≃ W)
    (target : X → V) (target' : Y → W)
    (htarget : ∀ x, target' (e.state x) = value (target x)) :
    DemandIso (experimentProblem q step target) (experimentProblem q' step' target') where
  demands := e.state
  witnesses := experimentEquiv e.action e.record value
  satisfaction test x := by
    change evaluate q' step' (translate e.action e.record value test) (e.state x) =
      target' (e.state x) ↔ evaluate q step test x = target x
    rw [e.evaluate_translate, htarget, value.injective.eq_iff]

theorem experiment_actual_trace_transport {X Y A B Q R V W : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (value : V ≃ W)
    (test : Experiment A Q V) (x : X) :
    executedTrace q' step' (translate e.action e.record value test) (e.state x) =
      (executedTrace q step test x).map e.action := e.executedTrace_translate value test x

theorem experiment_budget_transport {X Y A B Q R V W : Type*}
    {q : X → Q} {step : A → X → X} {q' : Y → R} {step' : B → Y → Y}
    (e : ObservationIso q step q' step') (value : V ≃ W)
    (target : X → V) (target' : Y → W)
    (htarget : ∀ x, target' (e.state x) = value (target x)) (budget : ℕ) :
    SolvesWithin q' step' target' budget ↔ SolvesWithin q step target budget :=
  solvesWithin_transport_iff e value target target' htarget budget

/-! ## Original finite equations and common probability laws -/

open scoped BigOperators

/-- Each demand retains one component of the supplied source equation. -/
def equationProblem {X I V : Type*} (observe : X → I → V) (rhs : I → V) : Problem I X where
  sat x i := observe x i = rhs i

/-- Linear rows retain their given indices and right sides. -/
def affineEquationProblem {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
    (rows : I → V →ₗ[K] K) (b : I → K) : Problem I V :=
  equationProblem (fun x i => rows i x) b

theorem affine_equations_good_iff {K V I : Type} [Field K] [AddCommGroup V]
    [Module K V] (rows : I → V →ₗ[K] K) (b : I → K) :
    Good (affineEquationProblem rows b) Set.univ ↔
      ∃ x, OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.Satisfies rows b x := by
  simp only [Good, Witnesses, affineEquationProblem, equationProblem,
    OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.Satisfies,
    Set.mem_setOf_eq, Set.mem_univ, forall_true_left]

/-- A failed common source valuation has a certificate in the original finite rows. -/
theorem affine_equations_refutation_iff {K V I : Type} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (rows : I → V →ₗ[K] K) (b : I → K) :
    ¬ Good (affineEquationProblem rows b) Set.univ ↔
      ∃ c : I → K, (∑ i, c i • rows i) = 0 ∧ (∑ i, c i * b i) ≠ 0 := by
  rw [affine_equations_good_iff]
  exact OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_solution_iff_row_refutation rows b

/-- The affine adapter includes the target certificate or a target-changing kernel direction. -/
theorem affine_source_certificate_trichotomy {K V I : Type} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (rows : I → V →ₗ[K] K) (b : I → K)
    (L : V →ₗ[K] K) :
    (∃ c : I → K, (∑ i, c i • rows i) = 0 ∧ (∑ i, c i * b i) ≠ 0) ∨
    (∃ (p : V) (c : I → K), p ∈ Witnesses (affineEquationProblem rows b) Set.univ ∧
      (∑ i, c i • rows i) = L) ∨
    (∃ p k, p ∈ Witnesses (affineEquationProblem rows b) Set.univ ∧
      (∀ i, rows i k = 0) ∧ L k ≠ 0) := by
  simpa only [Witnesses, affineEquationProblem, equationProblem,
    OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.Satisfies,
    Set.mem_setOf_eq, Set.mem_univ, forall_true_left] using
    OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.source_certificate_trichotomy rows b L

/-- An invertible change of the complete report vector keeps the common solution set. -/
theorem equation_vector_change_global {X I J V U : Type*}
    (observe : X → I → V) (b : I → V) (e : (I → V) ≃ (J → U)) :
    Witnesses (equationProblem (fun x => e (observe x)) (e b)) Set.univ =
      Witnesses (equationProblem observe b) Set.univ := by
  ext x
  change (∀ i ∈ Set.univ, e (observe x) i = e b i) ↔
    ∀ i ∈ Set.univ, observe x i = b i
  simp only [Set.mem_univ, forall_true_left]
  rw [← funext_iff, e.injective.eq_iff, funext_iff]

theorem affine_invertible_rows_keep_solutions {K V I J : Type} [Field K]
    [AddCommGroup V] [Module K V] (M : V →ₗ[K] (I → K))
    (R : (I → K) ≃ₗ[K] (J → K)) (b : I → K) :
    Witnesses (equationProblem (fun x => R (M x)) (R b)) Set.univ =
      Witnesses (equationProblem M b) Set.univ :=
  equation_vector_change_global M b R.toEquiv

/-- Subtracting the first report from the second is an invertible row operation. -/
def rowShear : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, v 1 - v 0]
  invFun v := ![v 0, v 1 + v 0]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by
    ext i
    fin_cases i
    · rfl
    · change (v 1 + w 1) - (v 0 + w 0) = (v 1 - v 0) + (w 1 - w 0)
      ring
  map_smul' a v := by
    ext i
    fin_cases i
    · rfl
    · change a * v 1 - a * v 0 = a * (v 1 - v 0)
      ring

/-- Global equation equivalence does not identify the restrictions to original row indices. -/
theorem row_mixing_changes_restrictions :
    Good (equationProblem (fun x : ℝ => ![x, x]) (![0, 1] : Fin 2 → ℝ))
      ({1} : Set (Fin 2)) ∧
    ¬ Good (equationProblem (fun x : ℝ => rowShear ![x, x]) (rowShear ![0, 1]))
      ({1} : Set (Fin 2)) ∧
    Witnesses (equationProblem (fun x : ℝ => rowShear ![x, x]) (rowShear ![0, 1])) Set.univ =
      Witnesses (equationProblem (fun x : ℝ => ![x, x]) (![0, 1] : Fin 2 → ℝ)) Set.univ := by
  refine ⟨?_, ?_, equation_vector_change_global _ _ rowShear.toEquiv⟩
  · refine ⟨1, ?_⟩
    intro i hi
    have he : i = 1 := Set.mem_singleton_iff.mp hi
    subst i
    norm_num [equationProblem]
  · rintro ⟨x, hx⟩
    have h := hx 1 (Set.mem_singleton 1)
    norm_num [equationProblem, rowShear] at h

/-- Candidates are normalized laws on the given complete assignments. -/
def AssignmentLaw (A : Type*) [Fintype A] :=
  {w : A → ℝ // (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1}

/-- Each demanded report is evaluated from the same candidate probability law. -/
def commonLawProblem {A J : Type*} [Fintype A] (v : A → J → ℝ)
    (p : J → ℝ) : Problem J (AssignmentLaw A) where
  sat w j := (∑ a, w.val a * v a j) = p j

/-- The adapter's common candidate is precisely the source-defined realization law. -/
theorem common_law_good_iff {A J : Type*} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) :
    Good (commonLawProblem v p) Set.univ ↔
      OperatorKO7.Meta.BoundaryObserver.ObserverRealization.Realizable v p := by
  constructor
  · rintro ⟨⟨w, hn, hs⟩, hw⟩
    refine ⟨w, hn, hs, ?_⟩
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hw j (Set.mem_univ j)
  · rintro ⟨w, hn, hs, hw⟩
    refine ⟨⟨w, hn, hs⟩, ?_⟩
    intro j _
    simpa only [commonLawProblem, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hw j

/-- Separation supplies a failed-demand certificate for the actual assignment law. -/
theorem common_law_obstruction_iff {A J : Type*} [Fintype A] [Fintype J]
    (v : A → J → ℝ) (p : J → ℝ) :
    ¬ Good (commonLawProblem v p) Set.univ ↔
      ∃ (c : J → ℝ) (b : ℝ),
        (∀ a, OperatorKO7.Meta.BoundaryObserver.ObserverRealization.reportScore c (v a) ≤ b) ∧
        b < OperatorKO7.Meta.BoundaryObserver.ObserverRealization.reportScore c p := by
  rw [common_law_good_iff]
  exact OperatorKO7.Meta.BoundaryObserver.ObserverRealization.not_realizable_iff_separating_score v p

/-- Every realized correction pays the source separating-score change. -/
theorem common_law_repair_bound {A J : Type*} [Fintype A] [Fintype J]
    (v : A → J → ℝ) (p r c : J → ℝ) (b : ℝ)
    (hr : Good (commonLawProblem v r) Set.univ)
    (hb : ∀ a, OperatorKO7.Meta.BoundaryObserver.ObserverRealization.reportScore c (v a) ≤ b) :
    OperatorKO7.Meta.BoundaryObserver.ObserverRealization.reportScore c p - b ≤
      ∑ j, |c j| * |p j - r j| :=
  OperatorKO7.Meta.BoundaryObserver.ObserverRealization.separating_score_repair_bound
    ((common_law_good_iff v r).mp hr) c b hb

/-- Repeated assignment labels leave every report-restriction problem unchanged in feasibility. -/
theorem common_law_reindex_good {A B J : Type*} [Fintype A] [Fintype B]
    (v : A → J → ℝ) (e : B → A) (he : Function.Surjective e) (p : J → ℝ) :
    Good (commonLawProblem (v ∘ e) p) Set.univ ↔
      Good (commonLawProblem v p) Set.univ := by
  rw [common_law_good_iff, common_law_good_iff]
  exact OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_iff_reindex v e he p

/-- The finite triangle is an instance of the common-law demand obstruction. -/
theorem triangle_demand_obstruction :
    ¬ Good (commonLawProblem
      OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangleReport (fun _ => 1)) Set.univ := by
  rw [common_law_good_iff]
  exact OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_not_realizable

/-! ## Complete licensed plans and their cost coordinates -/

/-- A plan carries its actual selector, component witnesses and both permissions. -/
def LicensedPlan {I W : Type*} (P : Problem I W) (menu : RepairMenu I W P)
    (D : Set I) (k : ℕ) :=
  {r : (I → Fin k) × (Fin k → W) // r.1 ∈ menu.allowed k ∧ menu.combines D k r.1 ∧
    ∀ i ∈ D, P.sat (r.2 (r.1 i)) i}

theorem licensedPlan_nonempty_iff {I W : Type*} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) (k : ℕ) :
    Nonempty (LicensedPlan P menu D k) ↔ RepairFeasible P menu D k := by
  constructor
  · rintro ⟨⟨⟨s, ws⟩, hs, hc, hw⟩⟩
    exact ⟨s, hs, hc, ws, hw⟩
  · rintro ⟨s, hs, hc, ws, hw⟩
    exact ⟨⟨(s, ws), hs, hc, hw⟩⟩

namespace DemandIso
variable {I J W V : Type*} {P : Problem I W} {Q : Problem J V}

/-- The whole licensed plan is transported, not merely its feasibility label. -/
def mapPlan (e : DemandIso P Q) (p : RepairMenu I W P) (q : RepairMenu J V Q)
    (hm : MenuCorrespondence e p q) (D : Set I) (k : ℕ)
    (r : LicensedPlan P p D k) : LicensedPlan Q q (e.demands '' D) k := by
  refine ⟨(e.selector r.val.1, fun j => e.witnesses (r.val.2 j)),
    (hm.allowed k r.val.1).mpr r.property.1,
    (hm.combines D k r.val.1).mpr r.property.2.1, ?_⟩
  rintro _ ⟨i, hi, rfl⟩
  simpa only [selector, e.demands.symm_apply_apply] using
    (e.satisfaction (r.val.2 (r.val.1 i)) i).mpr (r.property.2.2 i hi)

def unmapPlan (e : DemandIso P Q) (p : RepairMenu I W P) (q : RepairMenu J V Q)
    (hm : MenuCorrespondence e p q) (D : Set I) (k : ℕ)
    (r : LicensedPlan Q q (e.demands '' D) k) : LicensedPlan P p D k := by
  let s : I → Fin k := fun i => r.val.1 (e.demands i)
  have he : e.selector s = r.val.1 := by funext j; simp [selector, s]
  refine ⟨(s, fun j => e.witnesses.symm (r.val.2 j)),
    (hm.allowed k s).mp ?_, (hm.combines D k s).mp ?_, ?_⟩
  · simpa only [he] using r.property.1
  · simpa only [he] using r.property.2.1
  · intro i hi
    apply (e.satisfaction (e.witnesses.symm (r.val.2 (s i))) i).mp
    simpa only [s, e.witnesses.apply_symm_apply] using
      r.property.2.2 (e.demands i) ⟨i, hi, rfl⟩

def licensedPlanEquiv (e : DemandIso P Q) (p : RepairMenu I W P) (q : RepairMenu J V Q)
    (hm : MenuCorrespondence e p q) (D : Set I) (k : ℕ) :
    LicensedPlan P p D k ≃ LicensedPlan Q q (e.demands '' D) k where
  toFun := e.mapPlan p q hm D k
  invFun := e.unmapPlan p q hm D k
  left_inv r := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      simp [mapPlan, unmapPlan, selector]
    · funext j
      simp [mapPlan, unmapPlan]
  right_inv r := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      simp [mapPlan, unmapPlan, selector]
    · funext j
      simp [mapPlan, unmapPlan]

end DemandIso

/-- Every plan cost may depend on its selector and component witnesses together. -/
def LicensedBudget {I W : Type*} (P : Problem I W) (menu : RepairMenu I W P)
    (D : Set I) (k : ℕ) (cost : LicensedPlan P menu D k → ℕ → ℝ) (budget : ℕ → ℝ) : Prop :=
  ∃ r, ∀ j, cost r j ≤ budget j

/-- Exact license and whole-plan cost laws preserve the entire feasible budget set. -/
theorem licensed_budget_transport_iff {I J W V : Type*} {P : Problem I W} {Q : Problem J V}
    (e : DemandIso P Q) (p : RepairMenu I W P) (q : RepairMenu J V Q)
    (hm : e.MenuCorrespondence p q) (D : Set I) (k : ℕ)
    (cost : LicensedPlan P p D k → ℕ → ℝ)
    (cost' : LicensedPlan Q q (e.demands '' D) k → ℕ → ℝ)
    (hc : ∀ r j, cost' (e.licensedPlanEquiv p q hm D k r) j = cost r j) (budget : ℕ → ℝ) :
    LicensedBudget P p D k cost budget ↔
      LicensedBudget Q q (e.demands '' D) k cost' budget := by
  let iso := e.licensedPlanEquiv p q hm D k
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨iso r, fun j => (hc r j).trans_le (hr j)⟩
  · rintro ⟨r, hr⟩
    refine ⟨iso.symm r, ?_⟩
    intro j
    have h := hc (iso.symm r) j
    change cost' (iso (iso.symm r)) j = cost (iso.symm r) j at h
    rw [iso.apply_symm_apply] at h
    exact h.symm.trans_le (hr j)

/-! ## Counted computation as an actual readout demand -/

/-! ## The incidence of retained instrument outputs -/
namespace InstrumentAdapter
open OperatorKO7.Meta.BoundaryObserver
open InstrumentLoss InstrumentComposition

def instrumentProblem {X Y Z V : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) (P : X → V) := supportProblem (jointChannel I).prob P

/-- The side selector reads only the original input, not the sampled output. -/
theorem instrument_selected_iff {X Y Z V : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) (P : X → V) (k : ℕ) (side : X → Fin k) :
    Selected (instrumentProblem I P) k (fun xy => side xy.val.1) ↔
      ∃ d, StochasticGraph.Decodes (jointChannel I).prob P side d := by
  constructor
  · rintro ⟨ws, hw⟩
    exact ⟨fun out => ws out.2 out.1, fun x yz hx => hw ⟨(x, yz), hx⟩⟩
  · rintro ⟨d, hd⟩
    exact ⟨fun j yz => d (yz, j), fun xy => hd xy.val.1 xy.val.2 xy.property⟩

/-- Exact joint restoration is exactly global satisfaction of the source identity demands. -/
theorem instrument_recovery_good_iff {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) :
    Good (instrumentProblem I id) Set.univ ↔ StochasticRecoverable I := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, fun x y z hx => hr ⟨(x, (y, z)), hx⟩ (Set.mem_univ _)⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, fun xy _ => hr xy.val.1 xy.val.2.1 xy.val.2.2 xy.property⟩

/-- The native composition's complete kernel is used by the incidence object. -/
theorem composed_kernel_source {X Y Z W T : Type*}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (x : X) (y : Y) (w : W) (t : T) :
    (jointChannel (sequential I J)).prob x ((y, w), t) =
      ∑ z, I.weight x y z * (J y).weight z w t := rfl

/-- A normalized continuation cannot repair an input conflict without a new side selector. -/
theorem selected_before_of_after {X Y Z W T V : Type*} [Nonempty V]
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (k : ℕ) (side : X → Fin k) :
    Selected (instrumentProblem (sequential I J) P) k (fun xy => side xy.val.1) →
      Selected (instrumentProblem I P) k (fun xy => side xy.val.1) := by
  intro h
  exact (instrument_selected_iff I P k side).mpr
    (side_decoder_before_of_after I J P side
      ((instrument_selected_iff (sequential I J) P k side).mp h))

/-- Restoring continuations preserve each exact input-side selector budget. -/
theorem restoring_selected_iff {X Y Z W T V : Type*} [Nonempty V]
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (k : ℕ) (side : X → Fin k) (hJ : ∀ y, StochasticRecoverable (J y)) :
    Selected (instrumentProblem (sequential I J) P) k (fun xy => side xy.val.1) ↔
      Selected (instrumentProblem I P) k (fun xy => side xy.val.1) := by
  rw [instrument_selected_iff, instrument_selected_iff]
  exact recoverable_continuation_decoder_iff I J P side hJ

/-- The same silent outcome accompanies a complete retention and a complete erasure. -/
theorem silent_keep_erase_incidence_control :
    Good (instrumentProblem (deterministic silentKeep) id) Set.univ ∧
      ¬ Good (instrumentProblem (deterministic silentErase) id) Set.univ := by
  constructor
  · apply (instrument_recovery_good_iff _).mpr
    apply (deterministic_restoration_iff silentKeep).mpr
    exact ⟨fun yz => yz.2, fun _ => rfl⟩
  · intro h
    obtain ⟨r, hr⟩ := (deterministic_restoration_iff silentErase).mp
      ((instrument_recovery_good_iff _).mp h)
    have h0 := hr false
    have h1 := hr true
    change r ((), false) = false at h0
    change r ((), false) = true at h1
    have he := h0.symm.trans h1
    cases he
end InstrumentAdapter

end UniversalObservation.Transport
