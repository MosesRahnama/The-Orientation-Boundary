import OperatorKO7.Meta.OperationalInexpressibility.LicenseLattice

/-!
# Agreement from the meet observer

Two observers with a common real weighting assign equal signed fiber ratios to an event whenever
those assignments are common knowledge at a state whose meet cell has nonzero weight. For a
nonnegative normalized weighting, the ratio is conditional probability. Common knowledge at a
state is containment of the fiber of the meet observer through that state.

Relation: fibers of two observers and of their meet.
Property: the common-knowledge characterization and the agreement theorem.
Trust: kernel only; sums use classical decidability.
Scope: finite states; real weights of any sign; arbitrary observation types.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.AumannAgreement

open OperatorKO7.Meta.OperationalInexpressibility.LicenseLattice

open Classical

universe u v w

variable {X : Type u} [Fintype X] {Q₁ : Type v} {Q₂ : Type w}

/-- The weight of the states satisfying `C`. -/
noncomputable def massOf (μ : X → ℝ) (C : X → Prop) : ℝ := ∑ x, if C x then μ x else 0

/-- Observer `q` assigns the signed fiber ratio `a` to the event `E` at state `y`.  This equation
does not require nonnegative or normalized weights. -/
def AssignsFiberRatio {Q : Type*} (μ : X → ℝ) (q : X → Q) (E : X → Prop) (a : ℝ)
    (y : X) : Prop :=
  massOf μ (fun z => q z = q y ∧ E z) = a * massOf μ (fun z => q z = q y)

/-- Compatibility name.  Under a nonnegative normalized law, the fiber ratio is the usual
conditional probability. -/
def AssignsProbability {Q : Type*} (μ : X → ℝ) (q : X → Q) (E : X → Prop) (a : ℝ) (y : X) : Prop :=
  massOf μ (fun z => q z = q y ∧ E z) = a * massOf μ (fun z => q z = q y)

/-- The historical probability predicate and the signed fiber-ratio predicate are extensionally
identical. -/
theorem assignsFiberRatio_iff_assignsProbability {Q : Type*} (μ : X → ℝ) (q : X → Q)
    (E : X → Prop) (a : ℝ) (y : X) :
    AssignsFiberRatio μ q E a y ↔ AssignsProbability μ q E a y :=
  Iff.rfl

/-- The meet cell of `ω`. -/
def MeetCell (q₁ : X → Q₁) (q₂ : X → Q₂) (ω y : X) : Prop :=
  commonCoarsening q₁ q₂ y = commonCoarsening q₁ q₂ ω

/-- Common knowledge of `C` at `ω`. -/
def CommonKnowledgeAt (q₁ : X → Q₁) (q₂ : X → Q₂) (C : X → Prop) (ω : X) : Prop :=
  ∀ y, Relation.ReflTransGen (fun a b => q₁ a = q₁ b ∨ q₂ a = q₂ b) ω y → C y

omit [Fintype X] in
theorem commonKnowledgeAt_iff_meetCell (q₁ : X → Q₁) (q₂ : X → Q₂) (C : X → Prop) (ω : X) :
    CommonKnowledgeAt q₁ q₂ C ω ↔ ∀ y, MeetCell q₁ q₂ ω y → C y := by
  have key : ∀ a b : X,
      Relation.EqvGen (fun a b => q₁ a = q₁ b ∨ q₂ a = q₂ b) a b ↔
        Relation.ReflTransGen (fun a b => q₁ a = q₁ b ∨ q₂ a = q₂ b) a b := by
    intro a b
    constructor
    · intro h
      induction h with
      | rel x y hab => exact Relation.ReflTransGen.single hab
      | refl x => exact Relation.ReflTransGen.refl
      | symm x y hab ih =>
        exact Relation.ReflTransGen.symmetric
          (fun a b h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)) ih
      | trans x y z hab hbc ih₁ ih₂ => exact ih₁.trans ih₂
    · intro h
      induction h with
      | refl => exact Relation.EqvGen.refl _
      | tail hab hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)
  constructor
  · intro h y hy
    exact h y ((key ω y).mp
      (Relation.EqvGen.symm y ω ((commonCoarsening_eq_iff_eqvGen q₁ q₂ y ω).mp hy)))
  · intro h y hgen
    exact h y ((commonCoarsening_eq_iff_eqvGen q₁ q₂ y ω).mpr
      (Relation.EqvGen.symm ω y ((key ω y).mpr hgen)))

theorem massOf_eq_mul_of_saturated {Q : Type*} (μ : X → ℝ) (q : X → Q) (E : X → Prop) (a : ℝ)
    (Cell : X → Prop) (hsat : ∀ y z, q y = q z → (Cell y ↔ Cell z))
    (h : ∀ y, Cell y → AssignsProbability μ q E a y) :
    massOf μ (fun z => Cell z ∧ E z) = a * massOf μ Cell := by
  classical
  have hconv : ∀ (P : X → Prop) [DecidablePred P],
      (∑ z ∈ Finset.univ.filter P, μ z) = massOf μ P := by
    intro P _
    unfold massOf
    rw [Finset.sum_filter]
    first
    | rfl
    | apply Finset.sum_congr rfl
      intro x _
      by_cases h : P x <;> simp [h]
  set T := (Finset.univ.filter Cell).image q
  have hL1 : massOf μ (fun z => Cell z ∧ E z) =
      ∑ z ∈ Finset.univ.filter (fun z => Cell z ∧ E z), μ z := (hconv _).symm
  have hL2 : massOf μ Cell = ∑ z ∈ Finset.univ.filter Cell, μ z := (hconv Cell).symm
  have hmap1 : ∀ z ∈ Finset.univ.filter (fun z => Cell z ∧ E z), q z ∈ T := by
    intro z hz
    simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨z, hz.1, rfl⟩
  have hmap2 : ∀ z ∈ Finset.univ.filter Cell, q z ∈ T := by
    intro z hz
    simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨z, hz, rfl⟩
  have hf1 := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun z => Cell z ∧ E z))
    (t := T) (g := q) hmap1 (fun z => μ z)
  have hf2 := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter Cell)
    (t := T) (g := q) hmap2 (fun z => μ z)
  rw [hL1, hL2, ← hf1, ← hf2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨y₀, hy₀Cell, hy₀q⟩ := hj
  have h₁ : (Finset.univ.filter (fun z => Cell z ∧ E z)).filter (fun z => q z = j) =
      Finset.univ.filter (fun z => q z = q y₀ ∧ E z) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hzCell, hzE⟩, hzq⟩
      exact ⟨hzq.trans hy₀q.symm, hzE⟩
    · rintro ⟨hzq, hzE⟩
      exact ⟨⟨(hsat z y₀ hzq).mpr hy₀Cell, hzE⟩, hzq.trans hy₀q⟩
  have h₂ : (Finset.univ.filter Cell).filter (fun z => q z = j) =
      Finset.univ.filter (fun z => q z = q y₀) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hzCell, hzq⟩
      exact hzq.trans hy₀q.symm
    · intro hzq
      exact ⟨(hsat z y₀ hzq).mpr hy₀Cell, hzq.trans hy₀q⟩
  rw [h₁, h₂]
  rw [hconv (fun z => q z = q y₀ ∧ E z), hconv (fun z => q z = q y₀)]
  exact h y₀ hy₀Cell

omit [Fintype X] in
theorem meetCell_saturated_left (q₁ : X → Q₁) (q₂ : X → Q₂) (ω : X) :
    ∀ y z, q₁ y = q₁ z → (MeetCell q₁ q₂ ω y ↔ MeetCell q₁ q₂ ω z) := by
  intro y z hyz
  have hcc : commonCoarsening q₁ q₂ y = commonCoarsening q₁ q₂ z :=
    (commonCoarsening_eq_iff_eqvGen q₁ q₂ y z).mpr (Relation.EqvGen.rel y z (Or.inl hyz))
  unfold MeetCell
  rw [hcc]

omit [Fintype X] in
theorem meetCell_saturated_right (q₁ : X → Q₁) (q₂ : X → Q₂) (ω : X) :
    ∀ y z, q₂ y = q₂ z → (MeetCell q₁ q₂ ω y ↔ MeetCell q₁ q₂ ω z) := by
  intro y z hyz
  have hcc : commonCoarsening q₁ q₂ y = commonCoarsening q₁ q₂ z :=
    (commonCoarsening_eq_iff_eqvGen q₁ q₂ y z).mpr (Relation.EqvGen.rel y z (Or.inr hyz))
  unfold MeetCell
  rw [hcc]

private theorem massOf_eq_mul_of_saturated_fiberRatio {Q : Type*} (μ : X → ℝ)
    (q : X → Q) (E : X → Prop) (a : ℝ) (Cell : X → Prop)
    (hsat : ∀ y z, q y = q z → (Cell y ↔ Cell z))
    (h : ∀ y, Cell y → AssignsFiberRatio μ q E a y) :
    massOf μ (fun z => Cell z ∧ E z) = a * massOf μ Cell := by
  apply massOf_eq_mul_of_saturated μ q E a Cell hsat
  intro y hy
  exact (assignsFiberRatio_iff_assignsProbability μ q E a y).mp (h y hy)

/-- **Agreement theorem for signed fiber ratios.**  No positivity or normalization assumption is
placed on the state weights; only the meet cell must have nonzero total weight. -/
theorem agreement_of_commonKnowledge_fiberRatio (μ : X → ℝ) (q₁ : X → Q₁) (q₂ : X → Q₂)
    (E : X → Prop) (a b : ℝ) (ω : X) (hpos : massOf μ (MeetCell q₁ q₂ ω) ≠ 0)
    (hck : CommonKnowledgeAt q₁ q₂
      (fun y => AssignsFiberRatio μ q₁ E a y ∧ AssignsFiberRatio μ q₂ E b y) ω) :
    a = b := by
  rw [commonKnowledgeAt_iff_meetCell] at hck
  have h₁ := massOf_eq_mul_of_saturated_fiberRatio μ q₁ E a (MeetCell q₁ q₂ ω)
    (meetCell_saturated_left q₁ q₂ ω) (fun y hy => (hck y hy).1)
  have h₂ := massOf_eq_mul_of_saturated_fiberRatio μ q₂ E b (MeetCell q₁ q₂ ω)
    (meetCell_saturated_right q₁ q₂ ω) (fun y hy => (hck y hy).2)
  have hm : a * massOf μ (MeetCell q₁ q₂ ω) = b * massOf μ (MeetCell q₁ q₂ ω) :=
    h₁.symm.trans h₂
  exact mul_right_cancel₀ hpos hm

/-- Compatibility form of the agreement theorem, using the historical probability name. -/
theorem agreement_of_commonKnowledge (μ : X → ℝ) (q₁ : X → Q₁) (q₂ : X → Q₂) (E : X → Prop)
    (a b : ℝ) (ω : X) (hpos : massOf μ (MeetCell q₁ q₂ ω) ≠ 0)
    (hck : CommonKnowledgeAt q₁ q₂
      (fun y => AssignsProbability μ q₁ E a y ∧ AssignsProbability μ q₂ E b y) ω) :
    a = b := by
  rw [commonKnowledgeAt_iff_meetCell] at hck
  have h₁ := massOf_eq_mul_of_saturated μ q₁ E a (MeetCell q₁ q₂ ω)
    (meetCell_saturated_left q₁ q₂ ω) (fun y hy => (hck y hy).1)
  have h₂ := massOf_eq_mul_of_saturated μ q₂ E b (MeetCell q₁ q₂ ω)
    (meetCell_saturated_right q₁ q₂ ω) (fun y hy => (hck y hy).2)
  have hm : a * massOf μ (MeetCell q₁ q₂ ω) = b * massOf μ (MeetCell q₁ q₂ ω) := h₁.symm.trans h₂
  exact mul_right_cancel₀ hpos hm

/-- **Nonzero weight of the meet cell is required.** -/
theorem agreement_positive_mass_is_required :
    AssignsProbability (fun _ : Fin 2 => (0 : ℝ)) (fun _ => ()) (fun x => x = 0) 0 0 ∧
      AssignsProbability (fun _ : Fin 2 => (0 : ℝ)) (fun _ => ()) (fun x => x = 0) 1 0 := by
  constructor <;> simp [AssignsProbability, massOf]

/-- **Common knowledge is required.** Three states with equal weight, `E = {0}`, a constant
observer and the identity observer: at state `0` they assign `1/3` and `1`. -/
theorem agreement_commonKnowledge_is_required :
    AssignsProbability (fun _ : Fin 3 => (1 / 3 : ℝ)) (fun _ => ()) (fun x => x = 0) (1 / 3) 0 ∧
      AssignsProbability (fun _ : Fin 3 => (1 / 3 : ℝ)) (fun x => x) (fun x => x = 0) 1 0 ∧
      (1 / 3 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, by norm_num⟩
  · norm_num [AssignsProbability, massOf, Fin.sum_univ_three]
  · norm_num [AssignsProbability, massOf, Fin.sum_univ_three]

end OperatorKO7.Meta.OperationalInexpressibility.AumannAgreement
