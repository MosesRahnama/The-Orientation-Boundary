import OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

set_option autoImplicit false

/-!
# Finite demand obstructions and licensed repairs

The incidence relation retains candidates, original demands and combination permissions.
Empty obstructions are retained, including when the candidate type is empty.
-/

namespace UniversalObservation.Demand

universe u v w

structure Problem (I : Type u) (W : Type v) where
  sat : W → I → Prop

def Witnesses {I : Type u} {W : Type v} (P : Problem I W) (D : Set I) : Set W :=
  {x | ∀ i ∈ D, P.sat x i}

def Good {I : Type u} {W : Type v} (P : Problem I W) (D : Set I) : Prop :=
  ∃ x, x ∈ Witnesses P D

theorem witnesses_antitone {I : Type u} {W : Type v} (P : Problem I W)
    {D E : Set I} (h : D ⊆ E) : Witnesses P E ⊆ Witnesses P D :=
  fun _ hx i hi => hx i (h hi)

theorem good_downward {I : Type u} {W : Type v} (P : Problem I W)
    {D E : Set I} (h : D ⊆ E) : Good P E → Good P D := by
  rintro ⟨x, hx⟩
  exact ⟨x, witnesses_antitone P h hx⟩

theorem good_empty_iff {I : Type u} {W : Type v} (P : Problem I W) :
    Good P ∅ ↔ Nonempty W := by
  constructor
  · rintro ⟨x, _⟩; exact ⟨x⟩
  · rintro ⟨x⟩; exact ⟨x, fun _ h => h.elim⟩

def readoutProblem {X Y V : Type*} (O : X → Y) (T : X → V)
    (F : Set (Y → V)) : Problem X F where
  sat f x := f.val (O x) = T x

theorem readout_global_iff {X Y V : Type*} (O : X → Y) (T : X → V)
    (F : Set (Y → V)) :
    Good (readoutProblem O T F) Set.univ ↔
      OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds.Solvable O T F := by
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f.val, f.property, fun x => hf x (Set.mem_univ x)⟩
  · rintro ⟨f, hf, h⟩; exact ⟨⟨f, hf⟩, fun x _ => h x⟩

def MinimalBad {I : Type u} {W : Type v} (P : Problem I W) (B : Finset I) : Prop :=
  ¬ Good P (B : Set I) ∧ ∀ A : Finset I, A ⊂ B → Good P (A : Set I)

theorem exists_minimal_bad {I : Type u} {W : Type v} (P : Problem I W)
    (D : Finset I) : ¬ Good P (D : Set I) →
      ∃ B : Finset I, B ⊆ D ∧ MinimalBad P B := by
  classical
  refine Finset.strongInductionOn D ?_
  intro E ih hE
  by_cases hm : ∀ A : Finset I, A ⊂ E → Good P (A : Set I)
  · exact ⟨E, Finset.Subset.refl _, hE, hm⟩
  · push_neg at hm
    obtain ⟨A, hAE, hA⟩ := hm
    obtain ⟨B, hBA, hB⟩ := ih A hAE hA
    exact ⟨B, hBA.trans hAE.1, hB⟩

theorem finite_obstruction_iff {I : Type u} {W : Type v} (P : Problem I W)
    (D : Finset I) : ¬ Good P (D : Set I) ↔
      ∃ B : Finset I, B ⊆ D ∧ MinimalBad P B := by
  constructor
  · exact exists_minimal_bad P D
  · rintro ⟨B, hBD, hB⟩ hD
    exact hB.1 (good_downward P hBD hD)

theorem minimal_bad_nonempty {I : Type u} {W : Type v} [Nonempty W]
    (P : Problem I W) {B : Finset I} (hB : MinimalBad P B) : B.Nonempty := by
  classical
  by_contra h
  have hB0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  subst B
  exact hB.1 (by simpa using (good_empty_iff P).mpr inferInstance)

theorem minimal_bad_antichain {I : Type u} {W : Type v} (P : Problem I W)
    {A B : Finset I} (hA : MinimalBad P A) (hB : MinimalBad P B)
    (hAB : A ⊆ B) : A = B := by
  by_contra hne
  exact hA.1 (hB.2 A ⟨hAB, fun hBA => hne (Finset.Subset.antisymm hAB hBA)⟩)

def Downward {I : Type u} (K : Set (Set I)) : Prop :=
  ∀ D E, D ⊆ E → E ∈ K → D ∈ K

def membershipProblem {I : Type u} (K : Set (Set I)) : Problem I K where
  sat x i := i ∈ x.val

theorem membership_realizes {I : Type u} (K : Set (Set I)) (hK : Downward K)
    (D : Set I) : Good (membershipProblem K) D ↔ D ∈ K := by
  constructor
  · rintro ⟨x, hx⟩; exact hK D x.val hx x.property
  · intro hD; exact ⟨⟨D, hD⟩, fun _ hi => hi⟩

def booleanFamily {I : Type u} (K : Set (Set I)) : Set (I → Bool) :=
  {f | {i | f i = false} ∈ K}

theorem boolean_family_realizes {I : Type u} (K : Set (Set I)) (hK : Downward K)
    (D : Set I) : Good (readoutProblem id (fun _ => false) (booleanFamily K)) D ↔
      D ∈ K := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    exact hK D {i | f.val i = false} hf f.property
  · intro hD
    refine ⟨⟨fun i => if i ∈ D then false else true, ?_⟩, ?_⟩
    · change {i | (if i ∈ D then false else true) = false} ∈ K
      simpa using hD
    · intro i hi
      change (if i ∈ D then false else true) = false
      simp [hi]

theorem boolean_downset_realization {I : Type u} (K : Set (Set I))
    (hK : Downward K) (h0 : (∅ : Set I) ∈ K) :
    ∃ F : Set (I → Bool), F.Nonempty ∧ ∀ D : Set I,
      Good (readoutProblem id (fun _ => false) F) D ↔ D ∈ K := by
  refine ⟨booleanFamily K, ?_, boolean_family_realizes K hK⟩
  refine ⟨fun _ => true, ?_⟩
  change {i : I | true = false} ∈ K
  simpa using h0

def Selected {I : Type u} {W : Type v} (P : Problem I W) (k : ℕ)
    (s : I → Fin k) : Prop := ∃ xs : Fin k → W, ∀ i, P.sat (xs (s i)) i

def SelectedOn {I : Type u} {W : Type v} (P : Problem I W) (D : Set I)
    (k : ℕ) (s : I → Fin k) : Prop :=
  ∃ xs : Fin k → W, ∀ i ∈ D, P.sat (xs (s i)) i

def Colors {I : Type u} {W : Type v} (P : Problem I W) (k : ℕ)
    (s : I → Fin k) : Prop :=
  ∀ B : Finset I, MinimalBad P B → ¬ ∃ j : Fin k, ∀ i ∈ B, s i = j

def ColorsOn {I : Type u} {W : Type v} (P : Problem I W) (D : Set I)
    (k : ℕ) (s : I → Fin k) : Prop :=
  ∀ B : Finset I, (B : Set I) ⊆ D → MinimalBad P B →
    ¬ ∃ j : Fin k, ∀ i ∈ B, s i = j

theorem selectedOn_downward {I : Type u} {W : Type v} (P : Problem I W)
    {D E : Set I} (hDE : D ⊆ E) (k : ℕ) (s : I → Fin k) :
    SelectedOn P E k s → SelectedOn P D k s := by
  rintro ⟨xs, hx⟩; exact ⟨xs, fun i hi => hx i (hDE hi)⟩

theorem selectedOn_iff_colorsOn {I : Type u} [Fintype I] {W : Type v}
    (P : Problem I W) (D : Set I) (k : ℕ) (s : I → Fin k) :
    SelectedOn P D k s ↔ ColorsOn P D k s := by
  classical
  constructor
  · rintro ⟨xs, hx⟩ B hBD hB ⟨j, hj⟩
    apply hB.1
    refine ⟨xs j, ?_⟩
    intro i hi
    rw [← hj i hi]
    exact hx i (hBD hi)
  · intro hc
    have hgood (j : Fin k) : Good P {i | i ∈ D ∧ s i = j} := by
      by_contra hn
      let E : Finset I := Finset.univ.filter (fun i => i ∈ D ∧ s i = j)
      have hE : (E : Set I) = {i | i ∈ D ∧ s i = j} := by ext i; simp [E]
      obtain ⟨B, hBE, hB⟩ := (finite_obstruction_iff P E).mp (by simpa [hE] using hn)
      have hb (i : I) (hi : i ∈ B) : i ∈ D ∧ s i = j := by
        have := hBE hi
        simpa [E] using this
      exact hc B (fun i hi => (hb i hi).1) hB ⟨j, fun i hi => (hb i hi).2⟩
    choose xs hx using hgood
    exact ⟨xs, fun i hi => hx (s i) i ⟨hi, rfl⟩⟩

theorem selected_iff_colors {I : Type u} [Fintype I] {W : Type v}
    (P : Problem I W) (k : ℕ) (s : I → Fin k) : Selected P k s ↔ Colors P k s := by
  simpa [SelectedOn, Selected, ColorsOn, Colors] using
    selectedOn_iff_colorsOn P Set.univ k s

structure RepairMenu (I : Type u) (W : Type v) (P : Problem I W) where
  allowed : (k : ℕ) → Set (I → Fin k)
  combines : (D : Set I) → (k : ℕ) → (I → Fin k) → Prop

def RepairFeasible {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) (k : ℕ) : Prop :=
  ∃ s ∈ menu.allowed k, menu.combines D k s ∧ SelectedOn P D k s

theorem licensed_coloring_iff {I : Type u} [Fintype I] {W : Type v}
    (P : Problem I W) (menu : RepairMenu I W P) (D : Set I) (k : ℕ) :
    RepairFeasible P menu D k ↔
      ∃ s ∈ menu.allowed k, menu.combines D k s ∧ ColorsOn P D k s := by
  simp only [RepairFeasible, selectedOn_iff_colorsOn]

def CombinerSound {I W V : Type*} (P : Problem I W) (menu : RepairMenu I W P)
    (S : Problem I V) (assemble : (k : ℕ) → (I → Fin k) → (Fin k → W) → V) : Prop :=
  ∀ D k s xs, s ∈ menu.allowed k → menu.combines D k s →
    (∀ i ∈ D, P.sat (xs (s i)) i) → ∀ i ∈ D, S.sat (assemble k s xs) i

theorem source_repair_sound {I W V : Type*} (P : Problem I W)
    (menu : RepairMenu I W P) (S : Problem I V)
    (assemble : (k : ℕ) → (I → Fin k) → (Fin k → W) → V)
    (hs : CombinerSound P menu S assemble) (D : Set I) (k : ℕ) :
    RepairFeasible P menu D k → Good S D := by
  rintro ⟨s, ha, hc, xs, hx⟩
  exact ⟨assemble k s xs, hs D k s xs ha hc hx⟩


/-- Inclusion maximality needs every excluded demand, not a feasible subset alone. -/
def MaximalRetained {I W : Type*} (P : Problem I W) (D : Set I)
    (k : ℕ) (s : I → Fin k) : Prop :=
  SelectedOn P D k s ∧ ∀ E : Set I, D ⊆ E → SelectedOn P E k s → E = D

theorem hereditary_maximal_iff_insert {I : Type*} (K : Set I → Prop)
    (hK : ∀ D E, D ⊆ E → K E → K D) (D : Set I) :
    (K D ∧ ∀ E, D ⊆ E → K E → E = D) ↔
      K D ∧ ∀ i, i ∉ D → ¬ K (insert i D) := by
  classical
  constructor
  · rintro ⟨hD, hm⟩
    refine ⟨hD, ?_⟩
    intro i hi hI
    have he := hm (insert i D) (Set.subset_insert i D) hI
    exact hi (he ▸ Set.mem_insert i D)
  · rintro ⟨hD, hm⟩
    refine ⟨hD, ?_⟩
    intro E hDE hE
    apply Set.Subset.antisymm _ hDE
    intro i hi
    by_contra hn
    exact hm i hn (hK (insert i D) E (Set.insert_subset hi hDE) hE)

theorem maximal_retained_iff_insert {I W : Type*} (P : Problem I W)
    (D : Set I) (k : ℕ) (s : I → Fin k) :
    MaximalRetained P D k s ↔ SelectedOn P D k s ∧
      ∀ i, i ∉ D → ¬ SelectedOn P (insert i D) k s := by
  exact hereditary_maximal_iff_insert (fun E => SelectedOn P E k s)
    (fun _ _ h => selectedOn_downward P h k s) D

theorem maximal_retained_iff_obstruction {I : Type*} [Fintype I] {W : Type*}
    (P : Problem I W) (D : Set I) (k : ℕ) (s : I → Fin k) :
    MaximalRetained P D k s ↔ ColorsOn P D k s ∧
      ∀ i, i ∉ D → ∃ B : Finset I, i ∈ B ∧ (B : Set I) ⊆ insert i D ∧
        MinimalBad P B ∧ ∃ j : Fin k, ∀ x ∈ B, s x = j := by
  classical
  rw [maximal_retained_iff_insert]
  constructor
  · rintro ⟨hD, hm⟩
    have hc := (selectedOn_iff_colorsOn P D k s).mp hD
    refine ⟨hc, ?_⟩
    intro i hi
    have hn : ¬ ColorsOn P (insert i D) k s :=
      fun h => hm i hi ((selectedOn_iff_colorsOn P (insert i D) k s).mpr h)
    simp only [ColorsOn] at hn
    push_neg at hn
    obtain ⟨B, hBI, hB, hj⟩ := hn
    have hib : i ∈ B := by
      by_contra hni
      apply hc B _ hB hj
      intro x hx
      rcases hBI hx with hxi | hxD
      · subst x; exact (hni hx).elim
      · exact hxD
    exact ⟨B, hib, hBI, hB, hj⟩
  · rintro ⟨hc, hm⟩
    refine ⟨(selectedOn_iff_colorsOn P D k s).mpr hc, ?_⟩
    intro i hi hI
    obtain ⟨B, _, hBI, hB, hj⟩ := hm i hi
    exact (selectedOn_iff_colorsOn P (insert i D) k s).mp hI B hBI hB hj

/-- Permission itself may depend on the retained set and need not be hereditary. -/
def HereditaryMenu {I W : Type*} {P : Problem I W} (menu : RepairMenu I W P) : Prop :=
  ∀ D E, D ⊆ E → ∀ k s, s ∈ menu.allowed k →
    menu.combines E k s → menu.combines D k s

def MaximalLicensedRetained {I W : Type*} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) (k : ℕ) : Prop :=
  RepairFeasible P menu D k ∧
    ∀ E : Set I, D ⊆ E → RepairFeasible P menu E k → E = D

theorem repair_feasible_downward {I W : Type*} (P : Problem I W)
    (menu : RepairMenu I W P) (hmenu : HereditaryMenu menu)
    {D E : Set I} (hDE : D ⊆ E) (k : ℕ) :
    RepairFeasible P menu E k → RepairFeasible P menu D k := by
  rintro ⟨s, ha, hc, hs⟩
  exact ⟨s, ha, hmenu D E hDE k s ha hc, selectedOn_downward P hDE k s hs⟩

theorem maximal_licensed_iff_insert {I W : Type*} (P : Problem I W)
    (menu : RepairMenu I W P) (hmenu : HereditaryMenu menu) (D : Set I) (k : ℕ) :
    MaximalLicensedRetained P menu D k ↔ RepairFeasible P menu D k ∧
      ∀ i, i ∉ D → ¬ RepairFeasible P menu (insert i D) k := by
  exact hereditary_maximal_iff_insert (fun E => RepairFeasible P menu E k)
    (fun _ _ h => repair_feasible_downward P menu hmenu h k) D

theorem repair_feasible_menu_mono {I W : Type*} (P : Problem I W)
    (small large : RepairMenu I W P)
    (ha : ∀ k, small.allowed k ⊆ large.allowed k)
    (hc : ∀ D k s, small.combines D k s → large.combines D k s)
    (D : Set I) (k : ℕ) :
    RepairFeasible P small D k → RepairFeasible P large D k := by
  rintro ⟨s, hs, hl, hw⟩
  exact ⟨s, ha k hs, hc D k s hl, hw⟩

/-- None means no finite alphabet succeeds. It is not an exhausted search budget. -/
noncomputable def leastFinite (F : ℕ → Prop) : Option ℕ := by
  classical
  exact if h : ∃ k, F k then some (Nat.find h) else none

theorem leastFinite_none_iff (F : ℕ → Prop) :
    leastFinite F = none ↔ ∀ k, ¬ F k := by
  classical
  unfold leastFinite
  split_ifs with h
  · simp only [false_iff]
    push_neg
    exact h
  · simpa using h

theorem leastFinite_some_iff (F : ℕ → Prop) (k : ℕ) :
    leastFinite F = some k ↔ F k ∧ ∀ j, j < k → ¬ F j := by
  classical
  by_cases h : ∃ j, F j
  · simp only [leastFinite, dif_pos h, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩
    · rintro ⟨hk, hm⟩
      apply Nat.le_antisymm (Nat.find_min' h hk)
      by_contra hn
      exact hm (Nat.find h) (Nat.lt_of_not_ge hn) (Nat.find_spec h)
  · have hn : ¬ F k := fun hk => h ⟨k, hk⟩
    simp [leastFinite, h, hn]

noncomputable def minimumAlphabet {I W : Type*} (P : Problem I W) : Option ℕ :=
  leastFinite (fun k => ∃ s : I → Fin k, Selected P k s)

noncomputable def obstructionChromatic {I W : Type*} (P : Problem I W) : Option ℕ :=
  leastFinite (fun k => ∃ s : I → Fin k, Colors P k s)

theorem minimumAlphabet_eq_chromatic {I : Type*} [Fintype I] {W : Type*}
    (P : Problem I W) : minimumAlphabet P = obstructionChromatic P := by
  simp only [minimumAlphabet, obstructionChromatic, selected_iff_colors]

/-- All coordinate costs remain separate. A chosen scalar objective is optional. -/
def ParetoOptimal {A B : Type*} [Preorder B] (xs : Finset A) (cost : A → B) (x : A) : Prop :=
  x ∈ xs ∧ ∀ y ∈ xs, cost y ≤ cost x → cost x ≤ cost y

theorem finite_pareto_attainment {A B : Type*} [Preorder B]
    (xs : Finset A) (cost : A → B) (hxs : xs.Nonempty) :
    ∃ x, ParetoOptimal xs cost x := by
  classical
  induction xs using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hxs).elim
  | @insert a xs ha ih =>
    by_cases hn : xs.Nonempty
    · obtain ⟨x, hx, hm⟩ := ih hn
      by_cases hax : cost a ≤ cost x
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        intro y hy hya
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact le_rfl
        · exact hax.trans (hm y hy (hya.trans hax))
      · refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
        intro y hy hyx
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (hax hyx).elim
        · exact hm y hy hyx
    · have he : xs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst xs
      refine ⟨a, by simp, ?_⟩
      intro y hy _
      have : y = a := by simpa using hy
      subst y
      exact le_rfl

noncomputable def refusalMass {I : Type*} [Fintype I] (weight : I → ℝ)
    (D : Set I) : ℝ := by
  classical
  exact ∑ i, if i ∈ D then 0 else weight i

theorem refusalMass_antitone {I : Type*} [Fintype I] (weight : I → ℝ)
    (hn : ∀ i, 0 ≤ weight i) {D E : Set I} (hDE : D ⊆ E) :
    refusalMass weight E ≤ refusalMass weight D := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ D
  · simp [hi, hDE hi]
  · by_cases hj : i ∈ E
    · simp [hi, hj, hn i]
    · simp [hi, hj]

/-- All readouts on a nonempty answer type realize exactly the fiber-consistent targets. -/
theorem unrestricted_good_iff {X Y V : Type*} [Nonempty V]
    (O : X → Y) (T : X → V) (D : Set X) :
    Good (readoutProblem O T Set.univ) D ↔
      ∀ x ∈ D, ∀ y ∈ D, O x = O y → T x = T y := by
  classical
  constructor
  · rintro ⟨f, hf⟩ x hx y hy hxy
    exact (hf x hx).symm.trans ((congrArg f.val hxy).trans (hf y hy))
  · intro hc
    have hex : ∀ y : Y, ∃ v : V, ∀ x ∈ D, O x = y → v = T x := by
      intro y
      by_cases h : ∃ x ∈ D, O x = y
      · obtain ⟨x, hx, hxy⟩ := h
        exact ⟨T x, fun z hz hzy => hc x hx z hz (hxy.trans hzy.symm)⟩
      · exact ⟨Classical.choice inferInstance, fun x hx hxy => (h ⟨x, hx, hxy⟩).elim⟩
    choose f hf using hex
    exact ⟨⟨f, Set.mem_univ _⟩, fun x hx => hf (O x) x hx rfl⟩

theorem collision_pair_bad {X Y V : Type*} (O : X → Y) (T : X → V)
    (x y : X) (hO : O x = O y) (hT : T x ≠ T y) :
    ¬ Good (readoutProblem O T Set.univ) ({x, y} : Set X) := by
  rintro ⟨f, hf⟩
  exact hT ((hf x (by simp)).symm.trans ((congrArg f.val hO).trans (hf y (by simp))))

theorem minimal_bad_unrestricted_iff_pair {X Y V : Type*} [Nonempty V]
    [DecidableEq X] (O : X → Y) (T : X → V) (B : Finset X) :
    MinimalBad (readoutProblem O T Set.univ) B ↔
      ∃ x y : X, x ≠ y ∧ B = {x, y} ∧ O x = O y ∧ T x ≠ T y := by
  classical
  constructor
  · intro hB
    have hn := hB.1
    rw [unrestricted_good_iff] at hn
    push_neg at hn
    obtain ⟨x, hx, y, hy, hO, hT⟩ := hn
    have hxy : x ≠ y := fun h => hT (congrArg T h)
    have hsub : ({x, y} : Finset X) ⊆ B := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact (Finset.mem_singleton.mp hz) ▸ hy
    have he : B = {x, y} := by
      by_contra he
      have hs : ({x, y} : Finset X) ⊂ B :=
        ⟨hsub, fun h => he (Finset.Subset.antisymm h hsub)⟩
      exact collision_pair_bad O T x y hO hT (by simpa using hB.2 _ hs)
    exact ⟨x, y, hxy, he, hO, hT⟩
  · rintro ⟨x, y, hxy, rfl, hO, hT⟩
    refine ⟨by simpa using collision_pair_bad O T x y hO hT, ?_⟩
    intro A hA
    have hc : A.card < 2 := by simpa [Finset.card_pair hxy] using Finset.card_lt_card hA
    have h1 : A.card ≤ 1 := by omega
    apply (unrestricted_good_iff O T (A : Set X)).mpr
    intro a ha b hb _
    exact congrArg T (Finset.card_le_one.mp h1 a ha b hb)

/-- A three-way obstruction has no pair certificate. -/
def triple : Problem (Fin 3) (Fin 3) where
  sat x i := x ≠ i

theorem triple_global_failure : ¬ Good triple Set.univ := by
  rintro ⟨x, hx⟩
  exact hx x (Set.mem_univ x) rfl

theorem triple_every_pair : ∀ i j : Fin 3, ∃ x : Fin 3, x ≠ i ∧ x ≠ j := by decide

theorem triple_minimal_obstruction : MinimalBad triple (Finset.univ : Finset (Fin 3)) := by
  constructor
  · simpa using triple_global_failure
  · intro A hA
    have hn : ¬ Finset.univ ⊆ A := hA.2
    obtain ⟨x, _, hx⟩ := Finset.not_subset.mp hn
    exact ⟨x, fun i hi he => hx (he ▸ hi)⟩

theorem triple_two_selectors : Selected triple 2
    (fun i => if i = 0 then (0 : Fin 2) else 1) := by
  refine ⟨fun j => if j = 0 then (1 : Fin 3) else 0, ?_⟩
  intro i
  change (if (if i = 0 then (0 : Fin 2) else 1) = 0 then (1 : Fin 3) else 0) ≠ i
  by_cases hi : i = 0
  · subst i; decide
  · simpa [hi] using Ne.symm hi

theorem impossible_demand_blocks_selection {I W : Type*} (P : Problem I W)
    (i : I) (hn : ∀ w, ¬ P.sat w i) (k : ℕ) (s : I → Fin k) : ¬ Selected P k s := by
  rintro ⟨ws, hw⟩
  exact hn (ws (s i)) (hw i)

theorem empty_candidates_empty_obstruction {I : Type*} (P : Problem I Empty) :
    MinimalBad P ∅ := by
  constructor
  · rintro ⟨w, _⟩; exact w.elim
  · intro A hA; exact (Finset.not_ssubset_empty A hA).elim

/-- A permission-free coloring need not be a licensed repair. -/
def deniedMenu : RepairMenu Unit Unit (⟨fun _ _ => True⟩ : Problem Unit Unit) where
  allowed _ := Set.univ
  combines _ _ _ := False

theorem denied_menu_control :
    ColorsOn (⟨fun _ _ => True⟩ : Problem Unit Unit) Set.univ 1 (fun _ => 0) ∧
      ¬ RepairFeasible (⟨fun _ _ => True⟩ : Problem Unit Unit) deniedMenu Set.univ 1 := by
  constructor
  · apply (selectedOn_iff_colorsOn _ _ _ _).mp
    exact ⟨fun _ => (), fun _ _ => trivial⟩
  · rintro ⟨_, _, h, _⟩; exact h

/-- Executable finite enumeration, using only decidable finite quantifiers. -/
def finiteCheck (n m : ℕ) (table : Fin m → Fin n → Bool) : Bool :=
  decide (∃ w : Fin m, ∀ i : Fin n, table w i = true)

/-- M1.5 pilot: the actual executable checker reflects the source table. -/
theorem finiteCheck_correct (n m : ℕ) (table : Fin m → Fin n → Bool) :
    finiteCheck n m table = true ↔ ∃ w : Fin m, ∀ i : Fin n, table w i = true := by
  simp [finiteCheck]

/-- D3: every certificate is replayed against its complete source table. -/
def tableProblem {n m : ℕ} (table : Fin m → Fin n → Bool) : Problem (Fin n) (Fin m) where
  sat w i := table w i = true

def tableGood {n m : ℕ} (table : Fin m → Fin n → Bool) (D : Finset (Fin n)) : Bool :=
  decide (∃ w : Fin m, ∀ i ∈ D, table w i = true)

def minimalObstructions {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  D.powerset.filter (fun B => tableGood table B = false ∧
    ∀ A ∈ B.powerset, A ≠ B → tableGood table A = true)

inductive FiniteClaim (n m : ℕ)
  | witness (w : Fin m)
  | obstruction (B : Finset (Fin n))

structure FiniteEnvelope (n m : ℕ) where
  sourceTable : Fin m → Fin n → Bool
  demands : Finset (Fin n)
  claim : FiniteClaim n m

def FiniteClaimValid {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) : FiniteClaim n m → Prop
  | .witness w => ∀ i ∈ D, table w i = true
  | .obstruction B => B ⊆ D ∧ MinimalBad (tableProblem table) B

def replayEnvelope {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (c : FiniteEnvelope n m) : Bool :=
  decide (c.sourceTable = table ∧ c.demands = D) &&
    match c.claim with
    | .witness w => decide (∀ i ∈ D, table w i = true)
    | .obstruction B => decide (B ∈ minimalObstructions table D)

def subsetCandidates {T : Type} [DecidableEq T] : List T → List (Finset T)
  | [] => [∅]
  | x :: xs => let rest := subsetCandidates xs
               rest ++ rest.map (fun B : Finset T => insert x B)

def finiteSolve (n m : ℕ) (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) : Option (FiniteEnvelope n m) :=
  let claims := (List.ofFn (fun i : Fin m => i)).map FiniteClaim.witness ++
    (subsetCandidates (List.ofFn (fun i : Fin n => i))).map FiniteClaim.obstruction
  (claims.map (fun c => (⟨table, D, c⟩ : FiniteEnvelope n m))).find? (replayEnvelope table D)

/-- Complete finite search retains selector availability and combination permission. -/
def licensedSearch (n m k : ℕ) (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool) :
    Finset ((Fin n → Fin k) × (Fin k → Fin m)) :=
  Finset.univ.filter (fun sw => available sw.1 = true ∧ combines D sw.1 = true ∧
    ∀ i ∈ D, table (sw.2 (sw.1 i)) i = true)

/-- None claims exhaustive failure and is not a resource-halt certificate. -/
structure FiniteRepairEnvelope (n m k : ℕ) where
  sourceTable : Fin m → Fin n → Bool
  demands : Finset (Fin n)
  available : (Fin n → Fin k) → Bool
  combines : Finset (Fin n) → (Fin n → Fin k) → Bool
  claim : Option ((Fin n → Fin k) × (Fin k → Fin m))

def FiniteRepairClaimValid {n m k : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool) :
    Option ((Fin n → Fin k) × (Fin k → Fin m)) → Prop
  | some sw => available sw.1 = true ∧ combines D sw.1 = true ∧
      ∀ i ∈ D, table (sw.2 (sw.1 i)) i = true
  | none => ¬ ∃ (s : Fin n → Fin k) (ws : Fin k → Fin m), available s = true ∧ combines D s = true ∧
      ∀ i ∈ D, table (ws (s i)) i = true

def replayRepair {n m k : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool)
    (c : FiniteRepairEnvelope n m k) : Bool :=
  decide (c.sourceTable = table ∧ c.demands = D ∧ c.available = available ∧
      c.combines = combines) &&
    match c.claim with
    | some sw => decide (sw ∈ licensedSearch n m k table D available combines)
    | none => decide (licensedSearch n m k table D available combines = ∅)

/-- Finite function enumeration is structural and uses no noncomputable ordering. -/
def allAssignments : (n k : ℕ) → List (Fin n → Fin k)
  | 0, _ => [fun i => Fin.elim0 i]
  | n + 1, k => (List.ofFn (fun x : Fin k => x)).flatMap (fun x =>
      (allAssignments n k).map (fun tail => Fin.cases x tail))

def licensedSolve (n m k : ℕ) (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool) : FiniteRepairEnvelope n m k :=
  ⟨table, D, available, combines, ((allAssignments n k).flatMap (fun s =>
    (allAssignments k m).map (fun ws => (s, ws)))).find? (fun sw =>
      decide (sw ∈ licensedSearch n m k table D available combines))⟩


/-- A table test reflects the original incidence relation on its retained demands. -/
theorem tableGood_true_iff {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) : tableGood table D = true ↔ Good (tableProblem table) (D : Set (Fin n)) := by
  simp [tableGood, Good, Witnesses, tableProblem]

theorem tableGood_false_iff {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) : tableGood table D = false ↔ ¬ Good (tableProblem table) (D : Set (Fin n)) := by
  rw [← tableGood_true_iff]
  exact Bool.eq_false_iff

theorem minimalObstructions_mem_iff {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D B : Finset (Fin n)) :
    B ∈ minimalObstructions table D ↔ B ⊆ D ∧ MinimalBad (tableProblem table) B := by
  simp only [minimalObstructions, Finset.mem_filter, Finset.mem_powerset,
    tableGood_true_iff, tableGood_false_iff]
  constructor
  · rintro ⟨hBD, hbad, hmin⟩
    refine ⟨hBD, hbad, ?_⟩
    intro A hA
    exact hmin A hA.1 (fun he => hA.2 (he ▸ Finset.Subset.refl _))
  · rintro ⟨hBD, hbad, hmin⟩
    refine ⟨hBD, hbad, ?_⟩
    intro A hAB hne
    exact hmin A ⟨hAB, fun hBA => hne (Finset.Subset.antisymm hAB hBA)⟩

theorem replayEnvelope_correct {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (c : FiniteEnvelope n m) :
    replayEnvelope table D c = true ↔ c.sourceTable = table ∧ c.demands = D ∧
      FiniteClaimValid table D c.claim := by
  cases c with
  | mk source demands claim =>
    cases claim <;> simp [replayEnvelope, FiniteClaimValid, minimalObstructions_mem_iff, and_assoc]

theorem subsetCandidates_complete {T : Type} [DecidableEq T]
    (xs : List T) (B : Finset T) (hB : ∀ x ∈ B, x ∈ xs) : B ∈ subsetCandidates xs := by
  induction xs generalizing B with
  | nil =>
    have he : B = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro x hx
      exact List.not_mem_nil (hB x hx))
    simp [he, subsetCandidates]
  | cons x xs ih =>
    simp only [subsetCandidates, List.mem_append, List.mem_map]
    by_cases hx : x ∈ B
    · right
      refine ⟨B.erase x, ih _ ?_, Finset.insert_erase hx⟩
      intro y hy
      have he := Finset.mem_erase.mp hy
      exact (List.mem_cons.mp (hB y he.2)).resolve_left he.1
    · left
      apply ih
      intro y hy
      rcases List.mem_cons.mp (hB y hy) with he | he
      · exact (hx (he ▸ hy)).elim
      · exact he

/-- Total finite search returns a replayable proof or a replayable minimal obstruction. -/
theorem finite_solver_replays (n m : ℕ) (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) :
    ∃ c : FiniteEnvelope n m, finiteSolve n m table D = some c ∧ replayEnvelope table D c = true := by
  classical
  let claims := (List.ofFn (fun i : Fin m => i)).map FiniteClaim.witness ++
    (subsetCandidates (List.ofFn (fun i : Fin n => i))).map FiniteClaim.obstruction
  let candidates : List (FiniteEnvelope n m) := claims.map (fun c => ⟨table, D, c⟩)
  have hex : ∃ c ∈ candidates, replayEnvelope table D c = true := by
    by_cases h : Good (tableProblem table) (D : Set (Fin n))
    · obtain ⟨w, hw⟩ := h
      refine ⟨⟨table, D, .witness w⟩, ?_, ?_⟩
      · apply List.mem_map.mpr
        refine ⟨.witness w, ?_, rfl⟩
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨w, by simp, rfl⟩
      · exact (replayEnvelope_correct table D _).mpr ⟨rfl, rfl, hw⟩
    · obtain ⟨B, hBD, hB⟩ := exists_minimal_bad (tableProblem table) D h
      refine ⟨⟨table, D, .obstruction B⟩, ?_, ?_⟩
      · apply List.mem_map.mpr
        refine ⟨.obstruction B, ?_, rfl⟩
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨B, subsetCandidates_complete _ B (by intros; simp), rfl⟩
      · exact (replayEnvelope_correct table D _).mpr ⟨rfl, rfl, hBD, hB⟩
  cases he : candidates.find? (replayEnvelope table D) with
  | none =>
    obtain ⟨c, hc, hr⟩ := hex
    exact (List.find?_eq_none.mp he c hc hr).elim
  | some c =>
    exact ⟨c, he, List.find?_some he⟩

theorem wrong_source_replay_rejected {n m : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (c : FiniteEnvelope n m) (h : c.sourceTable ≠ table) :
    replayEnvelope table D c = false := by
  apply Bool.eq_false_iff.mpr
  intro hc
  exact h ((replayEnvelope_correct table D c).mp hc).1

theorem licensedSearch_mem_iff {n m k : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool)
    (sw : (Fin n → Fin k) × (Fin k → Fin m)) :
    sw ∈ licensedSearch n m k table D available combines ↔
      available sw.1 = true ∧ combines D sw.1 = true ∧ ∀ i ∈ D, table (sw.2 (sw.1 i)) i = true := by
  simp [licensedSearch]

theorem licensedSearch_empty_iff {n m k : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool) :
    licensedSearch n m k table D available combines = ∅ ↔
      ¬ ∃ (s : Fin n → Fin k) (ws : Fin k → Fin m), available s = true ∧ combines D s = true ∧
        ∀ i ∈ D, table (ws (s i)) i = true := by
  simp only [Finset.eq_empty_iff_forall_notMem, licensedSearch_mem_iff]
  constructor
  · intro h ⟨s, ws, hs⟩
    exact h (s, ws) hs
  · intro h sw hs
    exact h ⟨sw.1, sw.2, hs⟩

theorem replayRepair_correct {n m k : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool) (c : FiniteRepairEnvelope n m k) :
    replayRepair table D available combines c = true ↔
      c.sourceTable = table ∧ c.demands = D ∧ c.available = available ∧ c.combines = combines ∧
        FiniteRepairClaimValid table D available combines c.claim := by
  cases c with
  | mk source demands av co claim =>
    cases claim <;>
      simp [replayRepair, FiniteRepairClaimValid, licensedSearch_empty_iff, licensedSearch_mem_iff, and_assoc]

theorem allAssignments_complete (n k : ℕ) (f : Fin n → Fin k) : f ∈ allAssignments n k := by
  induction n with
  | zero =>
    have hf : f = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact i.elim0
    simp [allAssignments, hf]
  | succ n ih =>
    simp only [allAssignments, List.mem_flatMap, List.mem_map]
    refine ⟨f 0, by simp, (fun i => f i.succ), ih _, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The negative branch is justified by exhaustive finite search, never by a timeout. -/
theorem licensed_solver_replays (n m k : ℕ) (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool) :
    replayRepair table D available combines (licensedSolve n m k table D available combines) = true := by
  apply (replayRepair_correct table D available combines _).mpr
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  let pairs := (allAssignments n k).flatMap (fun s => (allAssignments k m).map (fun ws => (s, ws)))
  have hpairs (s : Fin n → Fin k) (ws : Fin k → Fin m) : (s, ws) ∈ pairs :=
    List.mem_flatMap.mpr ⟨s, allAssignments_complete n k s,
      List.mem_map.mpr ⟨ws, allAssignments_complete k m ws, rfl⟩⟩
  change FiniteRepairClaimValid table D available combines
    (pairs.find? (fun sw => decide (sw ∈ licensedSearch n m k table D available combines)))
  cases he : pairs.find? (fun sw => decide (sw ∈ licensedSearch n m k table D available combines)) with
  | none =>
    rintro ⟨s, ws, h⟩
    have hm := (licensedSearch_mem_iff table D available combines (s, ws)).mpr h
    exact List.find?_eq_none.mp he (s, ws) (hpairs s ws) (by simpa using hm)
  | some sw =>
    have hm := List.find?_some (p := fun t => decide (t ∈ licensedSearch n m k table D available combines)) (l := pairs) (a := sw) he
    exact (licensedSearch_mem_iff table D available combines sw).mp (of_decide_eq_true hm)

theorem licensedSearch_nonempty_iff {n m k : ℕ} (table : Fin m → Fin n → Bool)
    (D : Finset (Fin n)) (available : (Fin n → Fin k) → Bool)
    (combines : Finset (Fin n) → (Fin n → Fin k) → Bool)
    (menu : RepairMenu (Fin n) (Fin m) (tableProblem table))
    (ha : ∀ s, available s = true ↔ s ∈ menu.allowed k)
    (hc : ∀ (E : Finset (Fin n)) s, combines E s = true ↔ menu.combines (E : Set (Fin n)) k s) :
    (licensedSearch n m k table D available combines).Nonempty ↔
      RepairFeasible (tableProblem table) menu (D : Set (Fin n)) k := by
  constructor
  · rintro ⟨⟨s, ws⟩, h⟩
    obtain ⟨hs, hl, hw⟩ := (licensedSearch_mem_iff table D available combines (s, ws)).mp h
    exact ⟨s, (ha s).mp hs, (hc D s).mp hl, ws, hw⟩
  · rintro ⟨s, hs, hl, ws, hw⟩
    exact ⟨(s, ws), (licensedSearch_mem_iff table D available combines _).mpr
      ⟨(ha s).mpr hs, (hc D s).mpr hl, hw⟩⟩

/-- The three-demand table's only minimal obstruction is the whole triple. -/
theorem triple_table_certificate :
    minimalObstructions (fun w i : Fin 3 => decide (w ≠ i)) Finset.univ =
      {Finset.univ} := by decide

theorem singleton_table_certificate :
    minimalObstructions (fun _ : Fin 1 => fun _ : Fin 1 => false) Finset.univ =
      {Finset.univ} := by decide

theorem empty_witness_table_certificate :
    minimalObstructions (fun w : Fin 0 => (Fin.elim0 w : Fin 1 → Bool)) Finset.univ =
      {∅} := by decide

theorem denied_combination_search_empty :
    licensedSearch 1 1 1 (fun _ _ => true) Finset.univ (fun _ => true) (fun _ _ => false) = ∅ := by decide

/-! ## The least licensed alphabet of one retained set

The last sentence
of the licensed selector criterion. The two alphabets belong to one menu and one retained set `D`
and are read in `ℕ∞`, the natural numbers extended by `⊤`; the value `⊤` stands for the case in
which no finite alphabet succeeds. The pointwise criterion needs a finite retained set only, so the
demand carrier may be infinite; the hypothesis of the paper, a finite demand set, supplies a finite
`D`. The candidate type is arbitrary, the empty type included, and the size `0` is a size like any
other.
-/

/-- For a fixed selector and a finite retained set `D`, a selected family succeeds on `D` if and
only if no minimal obstruction contained in `D` is monochromatic. The demand carrier is
arbitrary; `selectedOn_iff_colorsOn` is the case of a finite carrier. -/
theorem selectedOn_iff_colorsOn_of_finite {I : Type u} {W : Type v} (P : Problem I W)
    {D : Set I} (hD : D.Finite) (k : ℕ) (s : I → Fin k) :
    SelectedOn P D k s ↔ ColorsOn P D k s := by
  classical
  constructor
  · rintro ⟨xs, hx⟩ B hBD hB ⟨j, hj⟩
    apply hB.1
    refine ⟨xs j, ?_⟩
    intro i hi
    rw [← hj i hi]
    exact hx i (hBD hi)
  · intro hc
    have hgood (j : Fin k) : Good P {i | i ∈ D ∧ s i = j} := by
      by_contra hn
      have hfin : ({i | i ∈ D ∧ s i = j} : Set I).Finite := hD.subset fun i hi => hi.1
      obtain ⟨B, hBE, hB⟩ :=
        (finite_obstruction_iff P hfin.toFinset).mp (by rwa [Set.Finite.coe_toFinset])
      have hb (i : I) (hi : i ∈ B) : i ∈ D ∧ s i = j := hfin.mem_toFinset.mp (hBE hi)
      exact hc B (fun i hi => (hb i hi).1) hB ⟨j, fun i hi => (hb i hi).2⟩
    choose xs hx using hgood
    exact ⟨xs, fun i hi => hx (s i) i ⟨hi, rfl⟩⟩

/-- The licensed coloring condition at size `k`: a permitted selector, with combination permission
on `D`, under which no minimal obstruction contained in `D` is monochromatic. -/
def LicensedColoring {I : Type u} {W : Type v} (P : Problem I W) (menu : RepairMenu I W P)
    (D : Set I) (k : ℕ) : Prop :=
  ∃ s ∈ menu.allowed k, menu.combines D k s ∧ ColorsOn P D k s

/-- The first sentence of the licensed selector criterion on a finite retained set `D` over an
arbitrary demand carrier: licensed feasibility at size `k` is licensed coloring at size `k`, with
the permitted selectors and the combination permission retained on both sides. -/
theorem licensed_coloring_iff_of_finite {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) {D : Set I} (hD : D.Finite) (k : ℕ) :
    RepairFeasible P menu D k ↔ LicensedColoring P menu D k := by
  simp only [RepairFeasible, LicensedColoring, selectedOn_iff_colorsOn_of_finite P hD]

/-- The least size `k : ℕ` with `F k`, read in `ℕ∞`: the infimum of the satisfying sizes, equal to
`⊤` if and only if no size satisfies `F`. The size `0` is included. -/
noncomputable def leastAlphabet (F : ℕ → Prop) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : F k), (k : ℕ∞)

/-- The infinite value: `leastAlphabet F = ⊤` if and only if no finite size satisfies `F`. -/
theorem leastAlphabet_eq_top_iff (F : ℕ → Prop) : leastAlphabet F = ⊤ ↔ ∀ k, ¬ F k := by
  unfold leastAlphabet
  rw [iInf_eq_top]
  refine forall_congr' fun k => ?_
  rw [iInf_eq_top]
  exact ⟨fun h hk => ENat.coe_ne_top k (h hk), fun h hk => (h hk).elim⟩

/-- `leastAlphabet` is `leastFinite` read in `ℕ∞`: the value `none` of `leastFinite` becomes `⊤`
and the value `some n` becomes `n`. -/
theorem leastAlphabet_eq_leastFinite (F : ℕ → Prop) :
    leastAlphabet F = (leastFinite F).elim ⊤ (fun n => (n : ℕ∞)) := by
  classical
  by_cases h : ∃ k, F k
  · have hl : leastFinite F = some (Nat.find h) :=
      (leastFinite_some_iff F _).mpr ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩
    rw [hl]
    show (⨅ (k : ℕ) (_ : F k), (k : ℕ∞)) = ((Nat.find h : ℕ) : ℕ∞)
    apply le_antisymm
    · exact iInf₂_le (Nat.find h) (Nat.find_spec h)
    · exact le_iInf₂ fun k hk => by exact_mod_cast Nat.find_min' h hk
  · have hn : ∀ k, ¬ F k := fun k hk => h ⟨k, hk⟩
    rw [(leastFinite_none_iff F).mpr hn]
    exact (leastAlphabet_eq_top_iff F).mpr hn

/-- A finite value of `leastAlphabet F`, the value `0` included, is the least size satisfying
`F`. -/
theorem leastAlphabet_eq_coe_iff (F : ℕ → Prop) (k : ℕ) :
    leastAlphabet F = (k : ℕ∞) ↔ F k ∧ ∀ j, j < k → ¬ F j := by
  rw [leastAlphabet_eq_leastFinite, ← leastFinite_some_iff F k]
  cases leastFinite F with
  | none => simp
  | some n => simp

/-- Equivalent conditions on the sizes have one least alphabet. -/
theorem leastAlphabet_congr {F G : ℕ → Prop} (h : ∀ k, F k ↔ G k) :
    leastAlphabet F = leastAlphabet G := by
  rw [show F = G from funext fun k => propext (h k)]

/-- The least feasible selector alphabet of one menu and one retained set, read in `ℕ∞`. -/
noncomputable def licensedMinimumAlphabet {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) : ℕ∞ :=
  leastAlphabet fun k => RepairFeasible P menu D k

/-- The least licensed coloring alphabet of one menu and one retained set, read in `ℕ∞`. -/
noncomputable def licensedColoringAlphabet {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) : ℕ∞ :=
  leastAlphabet fun k => LicensedColoring P menu D k

/-- The least feasible selector alphabet is `⊤` if and only if no finite size admits a licensed
selected family on `D`. -/
theorem licensedMinimumAlphabet_eq_top_iff {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) :
    licensedMinimumAlphabet P menu D = ⊤ ↔ ∀ k, ¬ RepairFeasible P menu D k :=
  leastAlphabet_eq_top_iff _

/-- The least licensed coloring alphabet is `⊤` if and only if no finite size admits a licensed
coloring of the minimal obstructions contained in `D`. -/
theorem licensedColoringAlphabet_eq_top_iff {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) :
    licensedColoringAlphabet P menu D = ⊤ ↔ ∀ k, ¬ LicensedColoring P menu D k :=
  leastAlphabet_eq_top_iff _

/-- A finite value `k` of the least feasible selector alphabet, `k = 0` included: size `k` admits
a licensed selected family on `D` and no smaller size does. -/
theorem licensedMinimumAlphabet_eq_coe_iff {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) (D : Set I) (k : ℕ) :
    licensedMinimumAlphabet P menu D = (k : ℕ∞) ↔
      RepairFeasible P menu D k ∧ ∀ j, j < k → ¬ RepairFeasible P menu D j :=
  leastAlphabet_eq_coe_iff _ k

/-- For one menu and one finite retained set, over an arbitrary demand carrier and an arbitrary
candidate type, the least feasible selector alphabet equals the least licensed coloring alphabet
in `ℕ∞`. -/
theorem licensedMinimumAlphabet_eq_coloring_of_finite {I : Type u} {W : Type v}
    (P : Problem I W) (menu : RepairMenu I W P) {D : Set I} (hD : D.Finite) :
    licensedMinimumAlphabet P menu D = licensedColoringAlphabet P menu D :=
  leastAlphabet_congr (licensed_coloring_iff_of_finite P menu hD)

/-- The same equality for `leastFinite`, the `Option ℕ` reading with `none` as the infinite
value: `leastFinite` applied to `licensed_coloring_iff_of_finite`. -/
theorem licensed_leastFinite_eq_of_finite {I : Type u} {W : Type v} (P : Problem I W)
    (menu : RepairMenu I W P) {D : Set I} (hD : D.Finite) :
    leastFinite (fun k => RepairFeasible P menu D k) =
      leastFinite (fun k => LicensedColoring P menu D k) := by
  rw [show (fun k => RepairFeasible P menu D k) = (fun k => LicensedColoring P menu D k) from
    funext fun k => propext (licensed_coloring_iff_of_finite P menu hD k)]

/-- The last sentence of the licensed selector criterion, `thm:licensed-selector`, for one menu and
one retained set `D` of a finite demand set: the least feasible selector alphabet equals the least
licensed coloring alphabet in `ℕ∞`; both sides take the infinite value `⊤` if and only if no
finite size succeeds; a finite value `k`, `k = 0` included, is the least feasible size. The
candidate type is arbitrary, the empty type included. -/
theorem licensed_selector_least_alphabet {I : Type u} [Finite I] {W : Type v}
    (P : Problem I W) (menu : RepairMenu I W P) (D : Set I) :
    licensedMinimumAlphabet P menu D = licensedColoringAlphabet P menu D ∧
      ((∀ k, ¬ RepairFeasible P menu D k) ↔
        licensedMinimumAlphabet P menu D = ⊤ ∧ licensedColoringAlphabet P menu D = ⊤) ∧
      ∀ k : ℕ, licensedMinimumAlphabet P menu D = (k : ℕ∞) ↔
        RepairFeasible P menu D k ∧ ∀ j, j < k → ¬ RepairFeasible P menu D j := by
  have he := licensedMinimumAlphabet_eq_coloring_of_finite P menu (Set.toFinite D)
  refine ⟨he, ?_, licensedMinimumAlphabet_eq_coe_iff P menu D⟩
  rw [← he, and_self, licensedMinimumAlphabet_eq_top_iff]

/-- The menu that permits every selector and every combination. -/
def permissiveMenu {I : Type u} {W : Type v} (P : Problem I W) : RepairMenu I W P where
  allowed _ := Set.univ
  combines _ _ _ := True

/-- Size `0` with no demand and no candidate: on the empty demand carrier and the empty candidate
type, the empty selector and the empty family succeed, and both least alphabets are `0`. -/
theorem licensed_alphabet_empty_carrier :
    licensedMinimumAlphabet (⟨fun _ _ => True⟩ : Problem Empty Empty) (permissiveMenu _)
        Set.univ = 0 ∧
      licensedColoringAlphabet (⟨fun _ _ => True⟩ : Problem Empty Empty) (permissiveMenu _)
        Set.univ = 0 := by
  have h0 : licensedMinimumAlphabet (⟨fun _ _ => True⟩ : Problem Empty Empty)
      (permissiveMenu _) Set.univ = ((0 : ℕ) : ℕ∞) :=
    (licensedMinimumAlphabet_eq_coe_iff _ _ _ 0).mpr
      ⟨⟨fun i => i.elim, Set.mem_univ _, trivial, fun j => j.elim0, fun i _ => i.elim⟩,
        fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rw [Nat.cast_zero] at h0
  have he := licensedMinimumAlphabet_eq_coloring_of_finite
    (⟨fun _ _ => True⟩ : Problem Empty Empty) (permissiveMenu _) (Set.toFinite Set.univ)
  exact ⟨h0, he.symm.trans h0⟩

/-- One demand and no candidate: for every retained set, the empty set included, both least
alphabets are `⊤`, since a selected family assigns a candidate to the selector value of the one
demand. -/
theorem licensed_alphabet_empty_candidates (D : Set Unit) :
    licensedMinimumAlphabet (⟨fun _ _ => True⟩ : Problem Unit Empty) (permissiveMenu _) D = ⊤ ∧
      licensedColoringAlphabet (⟨fun _ _ => True⟩ : Problem Unit Empty) (permissiveMenu _) D =
        ⊤ := by
  have ht : licensedMinimumAlphabet (⟨fun _ _ => True⟩ : Problem Unit Empty)
      (permissiveMenu _) D = ⊤ := by
    refine (licensedMinimumAlphabet_eq_top_iff _ _ _).mpr ?_
    rintro k ⟨s, -, -, xs, -⟩
    exact (xs (s ())).elim
  have he := licensedMinimumAlphabet_eq_coloring_of_finite
    (⟨fun _ _ => True⟩ : Problem Unit Empty) (permissiveMenu _) (Set.toFinite D)
  exact ⟨ht, he.symm.trans ht⟩

/-- The three-demand obstruction `triple` under the permissive menu: both least alphabets are `2`.
Size `0` has no selector on three demands, and at size `1` the whole triple is monochromatic. -/
theorem licensed_alphabet_triple :
    licensedMinimumAlphabet triple (permissiveMenu triple) Set.univ = 2 ∧
      licensedColoringAlphabet triple (permissiveMenu triple) Set.univ = 2 := by
  have h2 : licensedMinimumAlphabet triple (permissiveMenu triple) Set.univ =
      ((2 : ℕ) : ℕ∞) := by
    refine (licensedMinimumAlphabet_eq_coe_iff _ _ _ 2).mpr ⟨?_, ?_⟩
    · obtain ⟨xs, hx⟩ := triple_two_selectors
      exact ⟨fun i => if i = 0 then (0 : Fin 2) else 1, Set.mem_univ _, trivial, xs,
        fun i _ => hx i⟩
    · intro j hj
      rintro ⟨s, -, -, xs, hx⟩
      have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · exact (s 0).elim0
      · have hs : s (xs 0) = 0 := Subsingleton.elim _ _
        exact hx (xs 0) (Set.mem_univ _) (by rw [hs])
  rw [Nat.cast_ofNat] at h2
  have he := licensedMinimumAlphabet_eq_coloring_of_finite triple (permissiveMenu triple)
    (Set.toFinite Set.univ)
  exact ⟨h2, he.symm.trans h2⟩

/-- A denied combination permission: under `deniedMenu` both least licensed alphabets are `⊤`,
while the permission-free alphabet `minimumAlphabet` of the same problem on the whole demand set
is `1`, so the licensed minimum differs from the alphabet of `minimumAlphabet_eq_chromatic`. -/
theorem licensed_alphabet_denied :
    licensedMinimumAlphabet (⟨fun _ _ => True⟩ : Problem Unit Unit) deniedMenu Set.univ = ⊤ ∧
      licensedColoringAlphabet (⟨fun _ _ => True⟩ : Problem Unit Unit) deniedMenu Set.univ = ⊤ ∧
      minimumAlphabet (⟨fun _ _ => True⟩ : Problem Unit Unit) = some 1 := by
  have ht : licensedMinimumAlphabet (⟨fun _ _ => True⟩ : Problem Unit Unit) deniedMenu
      Set.univ = ⊤ := by
    refine (licensedMinimumAlphabet_eq_top_iff _ _ _).mpr ?_
    rintro k ⟨_, _, h, _⟩
    exact h
  have he := licensedMinimumAlphabet_eq_coloring_of_finite
    (⟨fun _ _ => True⟩ : Problem Unit Unit) deniedMenu (Set.toFinite Set.univ)
  refine ⟨ht, he.symm.trans ht, ?_⟩
  refine (leastFinite_some_iff _ 1).mpr ⟨⟨fun _ => 0, fun _ => (), fun _ => trivial⟩, ?_⟩
  rintro j hj ⟨s, -⟩
  have hj0 : j = 0 := by omega
  subst hj0
  exact (s ()).elim0


end UniversalObservation.Demand

#check @UniversalObservation.Demand.maximal_retained_iff_obstruction
#check @UniversalObservation.Demand.maximal_licensed_iff_insert
#check @UniversalObservation.Demand.minimal_bad_unrestricted_iff_pair

#check @UniversalObservation.Demand.finite_solver_replays
#check @UniversalObservation.Demand.licensed_solver_replays
