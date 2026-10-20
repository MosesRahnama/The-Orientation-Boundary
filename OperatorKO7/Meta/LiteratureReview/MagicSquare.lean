import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
# ex:magic-square

The three positive row products and the column products positive, positive,
negative form a six-demand minimal obstruction on nine signed integer tests,
and no finite common probability law satisfies all six demands almost surely.

The file formalizes the assignment and common-law claims. The operator table
and the appended counted-recursion material are outside its scope.
The impossibility proof holds for all integer tables; the deletion witnesses
take only the values positive one and negative one.
-/

universe u

namespace MagicSquare

open scoped BigOperators

noncomputable section

abbrev Assignment := Fin 3 → Fin 3 → ℤ
abbrev Demand := Fin 3 ⊕ Fin 3

def Signed (t : Assignment) : Prop :=
  ∀ i j, t i j = 1 ∨ t i j = -1

def rowProduct (t : Assignment) (i : Fin 3) : ℤ :=
  ∏ j, t i j

def columnProduct (t : Assignment) (j : Fin 3) : ℤ :=
  ∏ i, t i j

def columnTarget (j : Fin 3) : ℤ :=
  if j = 2 then -1 else 1

def Satisfies (t : Assignment) (d : Demand) : Prop :=
  match d with
  | Sum.inl i => rowProduct t i = 1
  | Sum.inr j => columnProduct t j = columnTarget j

instance (t : Assignment) (d : Demand) : Decidable (Satisfies t d) := by
  cases d with
  | inl i =>
    change Decidable (rowProduct t i = 1)
    infer_instance
  | inr j =>
    change Decidable (columnProduct t j = columnTarget j)
    infer_instance

def Realizable (D : Finset Demand) : Prop :=
  ∃ t : Assignment, Signed t ∧ ∀ d ∈ D, Satisfies t d

def MinimalObstruction (D : Finset Demand) : Prop :=
  ¬Realizable D ∧
    ∀ E : Finset Demand, E ⊆ D → E ≠ D → Realizable E

lemma demand_count : Fintype.card Demand = 6 := by
  norm_num [Demand]

lemma row_column_products (t : Assignment) :
    (∏ i, rowProduct t i) = ∏ j, columnProduct t j := by
  exact Finset.prod_comm

lemma column_target_product :
    (∏ j : Fin 3, columnTarget j) = -1 := by
  norm_num [columnTarget, Fin.prod_univ_three]

lemma no_assignment (t : Assignment) :
    ¬∀ d : Demand, Satisfies t d := by
  intro h
  have hr : (∏ i, rowProduct t i) = (1 : ℤ) := by
    calc
      _ = ∏ _i : Fin 3, (1 : ℤ) := by
        apply Finset.prod_congr rfl
        intro i _
        exact h (Sum.inl i)
      _ = 1 := by simp
  have hc : (∏ j, columnProduct t j) = (-1 : ℤ) := by
    calc
      _ = ∏ j : Fin 3, columnTarget j := by
        apply Finset.prod_congr rfl
        intro j _
        exact h (Sum.inr j)
      _ = -1 := column_target_product
  have heq := row_column_products t
  rw [hr, hc] at heq
  norm_num at heq

lemma full_not_realizable :
    ¬Realizable (Finset.univ : Finset Demand) := by
  intro h
  obtain ⟨t, _, ht⟩ := h
  apply no_assignment t
  intro d
  exact ht d (Finset.mem_univ d)

/-- The table has exactly the omitted demand as its failed demand. -/
def witness (omitted : Demand) : Assignment :=
  match omitted with
  | Sum.inl i =>
    fun r c => if r = i ∧ c = 2 then -1 else 1
  | Sum.inr j =>
    fun r c =>
      if j = 2 then 1
      else if r = 0 ∧ (c = j ∨ c = 2) then -1 else 1

lemma witness_signed (omitted : Demand) :
    Signed (witness omitted) := by
  intro r c
  cases omitted with
  | inl i =>
    dsimp [witness]
    split_ifs <;> norm_num
  | inr j =>
    dsimp [witness]
    split_ifs <;> norm_num

lemma witness_satisfies_iff (omitted d : Demand) :
    Satisfies (witness omitted) d ↔ d ≠ omitted := by
  rcases omitted with i | i <;> rcases d with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp only [Satisfies, witness, rowProduct, columnProduct,
      columnTarget, Fin.prod_univ_three] <;>
    decide

lemma witness_satisfied_set (omitted : Demand) :
    Finset.univ.filter (Satisfies (witness omitted)) =
      Finset.univ.erase omitted := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, and_true, witness_satisfies_iff]

lemma witness_meets_five (omitted : Demand) :
    (Finset.univ.filter (Satisfies (witness omitted))).card = 5 := by
  rw [witness_satisfied_set,
    Finset.card_erase_of_mem (Finset.mem_univ omitted),
    Finset.card_univ, demand_count]

lemma delete_one_realizable (omitted : Demand) :
    Realizable (Finset.univ.erase omitted) := by
  exists witness omitted
  constructor
  · exact witness_signed omitted
  · intro d hd
    exact (witness_satisfies_iff omitted d).2 (Finset.mem_erase.mp hd).1

lemma proper_subset_realizable (D : Finset Demand)
    (hD : D ≠ Finset.univ) :
    Realizable D := by
  have hex : ∃ d : Demand, d ∉ D := by
    by_contra hn
    apply hD
    apply Finset.eq_univ_of_forall
    intro d
    by_contra hd
    exact hn ⟨d, hd⟩
  obtain ⟨omitted, homitted⟩ := hex
  exists witness omitted
  constructor
  · exact witness_signed omitted
  · intro d hd
    apply (witness_satisfies_iff omitted d).2
    intro heq
    apply homitted
    simpa only [heq] using hd

lemma full_is_minimal :
    MinimalObstruction (Finset.univ : Finset Demand) := by
  constructor
  · exact full_not_realizable
  · intro D _ hD
    exact proper_subset_realizable D hD

def demandProbability {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (tables : Ω → Assignment) (d : Demand) : ℝ :=
  ∑ ω, if Satisfies (tables ω) d then p ω else 0

def HasCommonLaw {Ω : Type*} [Fintype Ω]
    (tables : Ω → Assignment) : Prop :=
  ∃ p : Ω → ℝ,
    (∀ ω, 0 ≤ p ω) ∧
    (∑ ω, p ω) = 1 ∧
    ∀ d : Demand, demandProbability p tables d = 1

lemma exists_positive_atom {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (htotal : (∑ ω, p ω) = 1) :
    ∃ ω, 0 < p ω := by
  by_contra hn
  have hz : ∀ ω, p ω = 0 := by
    intro ω
    have hnot : ¬0 < p ω := fun h => hn ⟨ω, h⟩
    exact le_antisymm (le_of_not_gt hnot) (hp ω)
  have hsum : (∑ ω, p ω) = 0 :=
    Finset.sum_eq_zero (fun ω _ => hz ω)
  linarith

lemma positive_atom_satisfies {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (tables : Ω → Assignment)
    (hp : ∀ ω, 0 ≤ p ω) (htotal : (∑ ω, p ω) = 1)
    (d : Demand) (hd : demandProbability p tables d = 1)
    (ω : Ω) (hω : 0 < p ω) :
    Satisfies (tables ω) d := by
  by_contra hbad
  have hnonneg :
      ∀ x, 0 ≤ (if Satisfies (tables x) d then 0 else p x) := by
    intro x
    split_ifs
    · exact le_rfl
    · exact hp x
  have hsplit :
      demandProbability p tables d +
        (∑ x, if Satisfies (tables x) d then 0 else p x) = 1 := by
    unfold demandProbability
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : Satisfies (tables x) d <;> simp [h]
      _ = 1 := htotal
  have hzero :
      (∑ x, if Satisfies (tables x) d then 0 else p x) = 0 := by
    rw [hd] at hsplit
    linarith
  have hsingle :
      (if Satisfies (tables ω) d then 0 else p ω) ≤
        ∑ x, if Satisfies (tables x) d then 0 else p x :=
    Finset.single_le_sum (fun x _ => hnonneg x) (Finset.mem_univ ω)
  rw [if_neg hbad, hzero] at hsingle
  exact (not_le_of_gt hω) hsingle

lemma no_common_law {Ω : Type*} [Fintype Ω]
    (tables : Ω → Assignment) :
    ¬HasCommonLaw tables := by
  intro h
  obtain ⟨p, hp, htotal, hdemands⟩ := h
  obtain ⟨ω, hω⟩ := exists_positive_atom p hp htotal
  apply no_assignment (tables ω)
  intro d
  exact positive_atom_satisfies p tables hp htotal d (hdemands d) ω hω

end

end MagicSquare

open MagicSquare

/-- The six-demand minimal obstruction of ex:magic-square. -/
theorem magic_square :
    Fintype.card Demand = 6 ∧
    (∀ t : Assignment, ¬∀ d : Demand, Satisfies t d) ∧
    MinimalObstruction (Finset.univ : Finset Demand) ∧
    (∀ omitted : Demand,
      Signed (witness omitted) ∧
      (∀ d : Demand, Satisfies (witness omitted) d ↔ d ≠ omitted) ∧
      (Finset.univ.filter (Satisfies (witness omitted))).card = 5 ∧
      Realizable (Finset.univ.erase omitted)) ∧
    (∀ (Ω : Type u) [Fintype Ω] (tables : Ω → Assignment),
      ¬HasCommonLaw tables) := by
  have hw (omitted : Demand) :
      Signed (witness omitted) ∧
      (∀ d : Demand, Satisfies (witness omitted) d ↔ d ≠ omitted) ∧
      (Finset.univ.filter (Satisfies (witness omitted))).card = 5 ∧
      Realizable (Finset.univ.erase omitted) :=
    ⟨witness_signed omitted, witness_satisfies_iff omitted,
      witness_meets_five omitted, delete_one_realizable omitted⟩
  exact ⟨demand_count, no_assignment, full_is_minimal, hw,
    fun Ω hΩ tables => @no_common_law Ω hΩ tables⟩

end OperatorKO7.Meta.LiteratureReview
