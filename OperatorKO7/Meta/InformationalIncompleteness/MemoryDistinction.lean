import OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
import OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy
import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.Physics.ConfessionLandauerSplit

/-!
# Memory, distinction, information: the mechanizable core of the triad

This module mechanizes the three theorem-shaped legs under the interpretive reading "duplication acts
as memory; memory is required to establish distinction; a registered distinction is information." The
*physical* reading (identifying these finite carriers with physical memory or physical measurement)
stays co-constitutive prose (ANALOGY-typed). The *finite-substrate* co-constitution is now a theorem
(`memory_distinction_information_equiv`, Leg 5): on a finite carrier the three faces are one
equivalence.

1. **Memory is necessary for distinction** (`equality_not_one_cell_observable`): on any carrier with
   two distinct elements, no observer that holds ONE cell decides equality; the comparator must hold
   both cells (`equality_is_two_cell_observable`). Holding both cells is the minimal memory.

2. **A registered distinction bears information** (`distinction_bears_information`): the fair two-point
   register carries entropy `H = log 2 > 0` (`H_coinFlip_eq_log_two`), while a register with no
   distinction (a point mass) carries exactly zero (`no_distinction_zero_information`, re-export of
   `H_pointMass`). Information is the registered distinction.

3. **The kernel's distinction primitive** (`eqW_distinction_fork`): the KO7 equality witness `eqW` maps
   the no-distinction cell `eqW a a` to `void` and manufactures structure from a pair; at the reflexive
   instance `eqW void void` the two rules fork to unjoinable normal forms (the existing W16.1 anomaly,
   re-exported). The distinction operation is exactly where the kernel's confluence boundary sits.

4. **Memory is free, the registered distinction is costed** (`memory_free_distinction_costed`): the
   Landauer floor is invariant under the redundant memory carrier and strictly positive on the
   committed record (re-export of the `ConfessionLandauerSplit` recursor witnesses).

5. **The triad as a theorem** (`memory_distinction_information_equiv`): on a finite carrier,
   `Nontrivial α` (a distinction exists) is equivalent both to the impossibility of a one-cell equality
   observer (two-cell memory is necessary) and to the existence of a register over `α` with strictly
   positive Shannon information. The three faces co-determine. This is the formal core of the
   co-constitutive reading; the physical gloss remains ANALOGY and carries no formal force.

## Claim typing (binding)
* PROVEN: the five legs above, each a Lean theorem below or a thin re-export of an existing
  baseline-clean anchor. Leg 5 is the finite-substrate co-constitution equivalence.
* ANALOGY (docstring only, never asserted by a theorem): any identification of these finite carriers
  with physical memory or physical measurement, and the dynamical "duplication manufactures the
  working-versus-recorded distinction" gloss.

## Audit slots
- Relation: the kernel `Step` relation appears only through the re-exported W16.1 anomaly; the new
  content is finite-alphabet information theory and a one-cell/two-cell observability split.
- Closure: `propext`, `Classical.choice`, `Quot.sound` (or a subset); verified by `#print axioms` below.
- Trust: no `sorry`/`admit`/`axiom`/`opaque`/`partial`/`unsafe`/`native_decide`/`bv_decide`/`@[csimp]`.
- Non-vacuity (R5): the one-cell impossibility is witnessed on `Bool` (`true ≠ false`); the two-cell
  comparator is exhibited; the coin-flip register has strictly positive entropy `log 2`; the Leg 5
  equivalence is witnessed non-degenerate on `Bool` (`memory_distinction_information_witness`).
- Scope: finite carriers only; the physical triad reading stays in docstrings.
-/

set_option autoImplicit false

noncomputable section

namespace OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.InformationalIncompleteness.DiagonalEntropy

/-! ## Leg 1: memory is necessary for distinction -/

/-- **Memory necessity.** On any carrier with two distinct elements, equality is NOT decidable by an
observer holding one cell: there is no `f : α → Bool` with `f x = true ↔ x = y` for all `x y`. The
comparison predicate is irreducibly a function of BOTH cells, so establishing a distinction requires
holding two values at once. Holding two values is the minimal memory. -/
theorem equality_not_one_cell_observable {α : Type} {a b : α} (hab : a ≠ b) :
    ¬ ∃ f : α → Bool, ∀ x y : α, (f x = true ↔ x = y) := by
  rintro ⟨f, hf⟩
  have ha : f a = true := (hf a a).mpr rfl
  exact hab ((hf a b).mp ha)

/-- **Two held cells suffice.** With decidable equality the two-cell comparator decides the
distinction: `decide (x = y) = true ↔ x = y`. Together with `equality_not_one_cell_observable` this
pins the minimal memory for a distinction at exactly two held cells. -/
theorem equality_is_two_cell_observable {α : Type} [DecidableEq α] :
    ∀ x y : α, (decide (x = y) = true ↔ x = y) := by
  intro x y
  exact decide_eq_true_iff

/-! ## Leg 2: a registered distinction bears information -/

/-- The fair two-point register: the minimal carrier of one registered distinction. -/
def coinFlip : Bool → ℝ := fun _ => 1 / 2

/-- The fair two-point register carries exactly one unit of information: `H coinFlip = log 2`. -/
theorem H_coinFlip_eq_log_two : H coinFlip = Real.log 2 := by
  unfold H coinFlip
  rw [Fintype.sum_bool]
  simp [Real.negMulLog, one_div, Real.log_inv]
  ring

/-- **A registered distinction is information.** The fair two-point register has strictly positive
entropy, `0 < H coinFlip = log 2`. -/
theorem distinction_bears_information : 0 < H coinFlip := by
  rw [H_coinFlip_eq_log_two]
  exact Real.log_pos (by norm_num)

/-- **No distinction, no information.** A register holding no distinction (a point mass) carries zero
entropy. Thin re-export of `H_pointMass`. -/
theorem no_distinction_zero_information {α : Type} [Fintype α] [DecidableEq α] (x₀ : α) :
    H (pointMass x₀) = 0 :=
  H_pointMass x₀

/-! ## Leg 3: the kernel's distinction primitive (re-export of the W16.1 anomaly) -/

open OperatorKO7 Trace in
/-- **The kernel distinction primitive forks at the no-distinction cell.** The KO7 equality witness
`eqW` is the kernel's distinction operation: `R_eq_refl` maps the no-distinction instance `eqW a a` to
`void`, and `R_eq_diff` manufactures structure from the pair. At `eqW void void` both rules fire and
the two normal forms are unjoinable (the W16.1 gauge anomaly): the distinction operation is exactly
where the kernel's confluence boundary sits. Thin re-export of
`EqWVoidAnomaly.local_confluence_fails_at_eqW_void_void`. -/
theorem eqW_distinction_fork :
    OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.CriticalPairAt
      (eqW void void) void (integrate (merge void void)) :=
  OperatorKO7.Meta.SafeStep.EqWVoidAnomaly.local_confluence_fails_at_eqW_void_void

/-! ## Leg 4: memory is free, the registered distinction is costed -/

open OperatorKO7.Meta.Physics.ConfessionLandauerSplit
open OperatorKO7.Meta.Physics.LandauerHeatBound in
/-- **Memory free, distinction costed.** On the recursor-shaped confession event: the Landauer floor is
invariant under the redundant memory carrier (five duplicated payload copies cost the same as zero),
while the committed record's floor is strictly positive (`log 2`). The memory is free; registering the
distinction is the costed event. Thin conjunction of the `ConfessionLandauerSplit` witnesses. -/
theorem memory_free_distinction_costed :
    (landauerLowerBound (recursorConfessionEvent 5) 1 1
        = landauerLowerBound (recursorConfessionEvent 0) 1 1)
    ∧ 0 < landauerLowerBound (recursorConfessionEvent 5) 1 1 :=
  ⟨recursorConfession_floor_indep_of_copies 1 1, recursorConfession_floor_pos⟩

/-! ## Leg 5: the co-constitution promoted to a theorem

The triad reading was previously ANALOGY-only. On a finite carrier the three faces are made one
equivalence: a distinction exists (`Nontrivial α`) iff no one-cell observer decides equality (two held
cells are the minimal necessary memory) iff some register over `α` bears strictly positive Shannon
information. The physical-memory and physical-measurement glosses stay ANALOGY. -/

/-- The injective two-point embedding `Bool → α` selecting two distinct carrier points
(`false ↦ a`, `true ↦ b`); injective exactly because `a ≠ b`. -/
def boolEmbed {α : Type} (a b : α) : Bool → α
  | false => a
  | true => b

/-- The two-point embedding is injective when the two chosen points differ. -/
theorem boolEmbed_injective {α : Type} {a b : α} (hab : a ≠ b) :
    Function.Injective (boolEmbed a b) := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolEmbed]

/-- Total mass is preserved by the pushforward: `∑_b (pushforward e p) b = ∑_a p a`. Each source point
`a` deposits its mass at the single image `e a`, so summing the pushforward over the target recovers the
source total. -/
theorem pushforward_total {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α → β) (p : α → ℝ) :
    ∑ b, pushforward e p b = ∑ a, p a := by
  unfold pushforward
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (e a) (fun _ => p a)]
  simp

/-- **The triad as a theorem.** On a finite carrier the three faces co-determine: a distinction exists
(`Nontrivial α`), iff no one-cell observer can decide equality so two held cells are necessary (the
minimal memory), iff some register over `α` bears strictly positive Shannon information. This is the
finite-substrate core of the co-constitutive reading; the physical-memory and physical-measurement
glosses remain ANALOGY and carry no formal force. -/
theorem memory_distinction_information_equiv {α : Type} [Fintype α] [DecidableEq α] :
    (Nontrivial α ↔ ¬ ∃ f : α → Bool, ∀ x y : α, (f x = true ↔ x = y))
      ∧ (Nontrivial α ↔ ∃ p : α → ℝ, (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1) ∧ 0 < H p) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- distinction ⇒ two-cell memory necessary
    intro _hD
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    exact equality_not_one_cell_observable hab
  · -- two-cell memory necessary ⇒ distinction
    intro hM
    by_contra hD
    rw [not_nontrivial_iff_subsingleton] at hD
    exact hM ⟨fun _ => true, fun x y => ⟨fun _ => Subsingleton.elim x y, fun _ => rfl⟩⟩
  · -- distinction ⇒ positive-information register
    intro _hD
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    refine ⟨pushforward (boolEmbed a b) coinFlip, ?_, ?_, ?_⟩
    · intro x
      unfold pushforward
      apply Finset.sum_nonneg
      intro c _
      split_ifs <;> norm_num [coinFlip]
    · rw [pushforward_total]
      simp only [coinFlip, Fintype.sum_bool]
      norm_num
    · rw [H_pushforward_injective (boolEmbed a b) (boolEmbed_injective hab) coinFlip]
      exact distinction_bears_information
  · -- positive-information register ⇒ distinction
    rintro ⟨p, _hp0, hp1, hppos⟩
    by_contra hD
    rw [not_nontrivial_iff_subsingleton] at hD
    rcases isEmpty_or_nonempty α with hα | hne
    · haveI := hα
      have hH : H p = 0 := by unfold H; simp
      rw [hH] at hppos; exact lt_irrefl 0 hppos
    · obtain ⟨x₀⟩ := hne
      have hpx : p x₀ = 1 := by
        rw [← hp1]
        symm
        refine Finset.sum_eq_single x₀ (fun b _ hb => absurd (Subsingleton.elim b x₀) hb) ?_
        intro h; exact absurd (Finset.mem_univ x₀) h
      have hH : H p = 0 := by
        unfold H
        rw [Finset.sum_eq_single x₀ (fun b _ hb => absurd (Subsingleton.elim b x₀) hb)
          (fun h => absurd (Finset.mem_univ x₀) h), hpx]
        simp [Real.negMulLog, Real.log_one]
      rw [hH] at hppos; exact lt_irrefl 0 hppos

/-- **Non-vacuity (R5).** The Leg 5 equivalence is non-degenerate: `Bool` realizes all three faces (a
distinction exists, no one-cell observer decides equality, and the fair register bears `log 2 > 0`); a
one-element carrier realizes none. -/
theorem memory_distinction_information_witness :
    Nontrivial Bool
      ∧ (¬ ∃ f : Bool → Bool, ∀ x y : Bool, (f x = true ↔ x = y))
      ∧ (∃ p : Bool → ℝ, (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1) ∧ 0 < H p) := by
  refine ⟨inferInstance, equality_not_one_cell_observable (show (true : Bool) ≠ false by decide), ?_⟩
  refine ⟨coinFlip, ?_, ?_, distinction_bears_information⟩
  · intro x; norm_num [coinFlip]
  · simp only [coinFlip, Fintype.sum_bool]; norm_num

/-! ## Axiom inventory (must be a subset of `{propext, Classical.choice, Quot.sound}`) -/

#print axioms equality_not_one_cell_observable
#print axioms equality_is_two_cell_observable
#print axioms H_coinFlip_eq_log_two
#print axioms distinction_bears_information
#print axioms no_distinction_zero_information
#print axioms eqW_distinction_fork
#print axioms memory_free_distinction_costed
#print axioms boolEmbed_injective
#print axioms pushforward_total
#print axioms memory_distinction_information_equiv
#print axioms memory_distinction_information_witness

end OperatorKO7.Meta.InformationalIncompleteness.MemoryDistinction
