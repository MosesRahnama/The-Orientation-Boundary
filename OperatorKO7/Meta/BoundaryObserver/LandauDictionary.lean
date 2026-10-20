import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import OperatorKO7.Meta.BoundaryObserver.NoReturn
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.BoundaryObserver.PairResolution
import OperatorKO7.Meta.BoundaryObserver.ApexInstance

set_option autoImplicit false

/-!
# The observer as a phase transition

The Landau dictionary of remark `rem:landau` consists of the group decomposition and
fiber orbits, the free transitive action on place coordinates, the entropy of a merge
and its inversion by an outside record, the absence of a return in terminating
relations, and the two-sided reading-cost pole of order one in positive
discrimination and order two in positive binary bias. The dictionary concerns
structural symmetry, not a thermodynamic limit or singularity of a partition function.

Proof graph: `Audit/ledgers/boundary-theorem/BOUNDARY-THEOREM-MATH-COMPLETION-PROOF-GRAPH.md`, N23.
-/

namespace OperatorKO7.Meta.BoundaryObserver.LandauDictionary

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
open OperatorKO7.Meta.BoundaryObserver.MergedPair
open OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
open OperatorKO7.Meta.BoundaryObserver.NoReturn
open OperatorKO7.Meta.BoundaryObserver.BitDivision
open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution
  (FiniteLaw FiniteProtocol HistoryBank terminalMI expectedCost historyBank)
open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity
open OperatorKO7.Meta.BoundaryObserver.BoundaryPole
open OperatorKO7.Meta.BoundaryObserver.PairResolution
open OperatorKO7.Meta.BoundaryObserver.ApexInstance

universe u v w

/-- The observer stabilizer is the product of the permutation groups of all attained
fibers. Its orbits are exactly the fibers, and it is trivial precisely for an
injective observer. -/
theorem landau_symmetry_change {X : Type u} {Q : Type v} (q : X → Q) :
    Nonempty (licenseStabilizer q ≃*
      (∀ y : Set.range q, Equiv.Perm (ObserverFiber q y))) ∧
    (∀ x y : X, q x = q y ↔ ∃ σ ∈ licenseStabilizer q, σ x = y) ∧
    (licenseStabilizer q = ⊥ ↔ Function.Injective q) := by
  exact ⟨⟨licenseStabilizerFiberMulEquiv q⟩,
    (fun x y => same_record_iff_orbit q x y),
    licenseStabilizer_eq_bot_iff_injective q⟩

/-- Every place coordinate resolves the observer into a bijective pair and removes the
boundary. Observer-preserving permutations act on place coordinates, freely and with one
orbit under composition with the inverse permutation. -/
theorem landau_order_parameter {X : Type u} {Q : Type v} (q : X → Q) (n : ℕ) :
    (∀ p : X → Fin n, p ∈ PlaceCoord q n →
      Function.Bijective (fun x => (Set.rangeFactorization q x, p x)) ∧
        boundary (fun x => (q x, p x)) = ∅) ∧
    (∀ (p : X → Fin n) (σ : Equiv.Perm X),
      p ∈ PlaceCoord q n → σ ∈ licenseStabilizer q →
        p ∘ σ.symm ∈ PlaceCoord q n) ∧
    (∀ (p : X → Fin n) (σ : Equiv.Perm X),
      p ∈ PlaceCoord q n → σ ∈ licenseStabilizer q →
        (p ∘ σ.symm = p → σ = 1)) ∧
    (∀ p p' : X → Fin n, p ∈ PlaceCoord q n → p' ∈ PlaceCoord q n →
      ∃ σ ∈ licenseStabilizer q, p' = p ∘ σ.symm) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have hbij := placeCoord_pair_bijective q hp
    refine ⟨hbij, ?_⟩
    apply (boundary_eq_empty_iff_injective (fun x => (q x, p x))).2
    intro a b hab
    have hq : q a = q b := congrArg (fun z : Q × Fin n => z.1) hab
    have hp' : p a = p b := congrArg (fun z : Q × Fin n => z.2) hab
    exact hbij.1 (Prod.ext (Subtype.ext hq) hp')
  · intro p σ hp hσ
    exact placeCoord_smul_mem q hp hσ
  · intro p σ hp hσ hfix
    exact placeCoord_free q hp hσ hfix
  · intro p p' hp hp'
    exact placeCoord_transitive q hp hp'

/-- For the uniform law on a finite nonempty state space, the entropy left by
an observer is the weighted logarithm of its fiber sizes. It is maximal exactly
for a constant observer. A constant record of a fair pair leaves `log 2`
natural units, and an outside record of `n` values permits inversion exactly
for observers with fibers of size at most `n`. -/
theorem landau_entropy_release {X : Type u} {Q : Type v}
    [Fintype X] [Fintype Q] [DecidableEq Q] [Nonempty X] (q : X → Q) :
    (entropy (fun _ : X => (1 : ℝ) / Fintype.card X) -
        entropy (fun y : Q =>
          ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) =
      ∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
        Real.log ((Finset.univ.filter (fun x => q x = y)).card)) ∧
    ((∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
        Real.log ((Finset.univ.filter (fun x => q x = y)).card)) =
      Real.log (Fintype.card X) ↔ ∀ x x', q x = q x') ∧
    (entropy (fun _ : Bool => (1 : ℝ) / 2) -
      entropy (fun _ : Unit => (1 : ℝ)) = Real.log 2) ∧
    (∀ n : ℕ,
      ((∃ s : X → Fin n,
        ∃ r : Set.range (fun x => (q x, s x)) → X,
          ∀ x, r (Set.rangeFactorization (fun x => (q x, s x)) x) = x) ↔
        ∀ y : Q, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n)) := by
  exact ⟨condEntropy_uniform q, condEntropy_uniform_eq_log_card_iff q,
    pair_condEntropy_one_bit, fun n => exists_inverting_record_iff q n⟩

/-- The record has an inverse on its attained values exactly for an injective
observer. A relation with no infinite forward chain has no nonempty path
returning to its starting point. -/
theorem landau_irreversibility {X : Type u} {Q : Type v} (q : X → Q) :
    ((∃ r : Set.range q → X,
      ∀ x, r (Set.rangeFactorization q x) = x) ↔ Function.Injective q) ∧
    (∀ (T : Type w) (r : T → T → Prop),
      (¬ ∃ f : ℕ → T, ∀ n, r (f n) (f (n + 1))) →
        ∀ t : T, ¬ Relation.TransGen r t t) := by
  exact ⟨left_inverse_iff_injective q,
    (fun _ r h t => no_return_of_no_infinite_seq r h t)⟩

/-- The finite pair reading has matching lower and upper order-one cost
bounds in its positive discrimination, and the binary symmetric reading has
the corresponding order-two bounds in positive bias, including residue
bounds for the least repeated-reading cost. -/
theorem landau_reading_pole :
  (∀ {Y : Type} [Fintype Y] (P Q : FiniteLaw Y),
      0 < discrimination P.mass Q.mass →
        (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Y) (c : ℝ),
          PairMenu p (discrimination P.mass Q.mass) →
          ∀ (n : ℕ) (bank : List (List (A × Y))), HistoryBank n bank →
            c ≤ terminalMI p n bank →
              c * Real.log 2 / discrimination P.mass Q.mass ≤ expectedCost p n bank) ∧
        (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
          1 - Real.binEntropy η / Real.log 2 ≤
              terminalMI (repeatProtocol P Q N) N (historyBank Unit Y N) ∧
            expectedCost (repeatProtocol P Q N) N (historyBank Unit Y N) = N ∧
            (N : ℝ) ≤ 4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass + 1)) ∧
    (∀ (ε : ℝ) (hε : |ε| ≤ 1 / 2), 0 < ε →
      readingDiscrimination (binaryRow ε hε) true false = 8 * ε ^ 2 ∧
      (∀ (A : Type) [Fintype A] (p : FiniteProtocol Bool A Bool) (c : ℝ),
        PairMenu p (8 * ε ^ 2) → ∀ n bank, HistoryBank n bank →
          c ≤ terminalMI p n bank → c * Real.log 2 ≤ 8 * ε ^ 2 * expectedCost p n bank) ∧
      (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
        1 - Real.binEntropy η / Real.log 2 ≤
            terminalMI (repeatProtocol (binaryRow ε hε true) (binaryRow ε hε false) N) N
              (historyBank Unit Bool N) ∧
          8 * ε ^ 2 * N ≤ 4 * Real.log (1 / (2 * η)) + 8 * ε ^ 2) ∧
      (∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        (1 - Real.binEntropy η / Real.log 2) * Real.log 2 ≤
            8 * ε ^ 2 * leastRepeatCost (binaryRow ε hε true) (binaryRow ε hε false)
              (1 - Real.binEntropy η / Real.log 2) ∧
          8 * ε ^ 2 * leastRepeatCost (binaryRow ε hε true) (binaryRow ε hε false)
              (1 - Real.binEntropy η / Real.log 2) ≤
            4 * Real.log (1 / (2 * η)) + 8 * ε ^ 2)) := by
  refine ⟨?_, ?_⟩
  · intro Y _ P Q hΔ
    exact PairResolution.pair_resolution_two_sided P Q hΔ
  · exact ApexInstance.binaryPoleGoal

/-- The five quantified parts of remark `rem:landau`: stabilizer symmetry,
free and transitive place coordinates, entropy and outside inversion, absence
of return under termination, and the two-sided reading-cost pole. Each part
has the full observer and relation domains of its supporting theorem. The entropy
part holds on any state space: beside the identities for a finite nonempty state
set, the uniform law on one finite fiber `C` inside arbitrary state and record
types leaves `log₂ (card C)` bits. -/
def LandauDictionaryGoal : Prop :=
  (∀ (X : Type u) (Q : Type v) (q : X → Q),
    Nonempty (licenseStabilizer q ≃*
          (∀ y : Set.range q, Equiv.Perm (ObserverFiber q y))) ∧
        (∀ x y : X, q x = q y ↔ ∃ σ ∈ licenseStabilizer q, σ x = y) ∧
        (licenseStabilizer q = ⊥ ↔ Function.Injective q)) ∧
  (∀ (X : Type u) (Q : Type v) (q : X → Q) (n : ℕ),
    (∀ p : X → Fin n, p ∈ PlaceCoord q n →
          Function.Bijective (fun x => (Set.rangeFactorization q x, p x)) ∧
            boundary (fun x => (q x, p x)) = ∅) ∧
        (∀ (p : X → Fin n) (σ : Equiv.Perm X),
          p ∈ PlaceCoord q n → σ ∈ licenseStabilizer q →
            p ∘ σ.symm ∈ PlaceCoord q n) ∧
        (∀ (p : X → Fin n) (σ : Equiv.Perm X),
          p ∈ PlaceCoord q n → σ ∈ licenseStabilizer q →
            (p ∘ σ.symm = p → σ = 1)) ∧
        (∀ p p' : X → Fin n, p ∈ PlaceCoord q n → p' ∈ PlaceCoord q n →
          ∃ σ ∈ licenseStabilizer q, p' = p ∘ σ.symm)) ∧
  ((∀ (X : Type u) (Q : Type v)
    [Fintype X] [Fintype Q] [DecidableEq Q] [Nonempty X] (q : X → Q),
    (entropy (fun _ : X => (1 : ℝ) / Fintype.card X) -
            entropy (fun y : Q =>
              ((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) =
          ∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
            Real.log ((Finset.univ.filter (fun x => q x = y)).card)) ∧
        ((∑ y : Q, (((Finset.univ.filter (fun x => q x = y)).card : ℝ) / Fintype.card X) *
            Real.log ((Finset.univ.filter (fun x => q x = y)).card)) =
          Real.log (Fintype.card X) ↔ ∀ x x', q x = q x') ∧
        (entropy (fun _ : Bool => (1 : ℝ) / 2) -
          entropy (fun _ : Unit => (1 : ℝ)) = Real.log 2) ∧
        (∀ n : ℕ,
          ((∃ s : X → Fin n,
            ∃ r : Set.range (fun x => (q x, s x)) → X,
              ∀ x, r (Set.rangeFactorization (fun x => (q x, s x)) x) = x) ↔
            ∀ y : Q, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n))) ∧
    (∀ (X : Type u) (Q : Type v) (q : X → Q) (C : Finset X) (hC : C.Nonempty),
      (∀ x ∈ C, ∀ x' ∈ C, q x = q x') →
        isolatedFiberUniformConditionalEntropy q C hC / Real.log 2 =
          Real.logb 2 C.card)) ∧
  (∀ (X : Type u) (Q : Type v) (q : X → Q),
    ((∃ r : Set.range q → X,
          ∀ x, r (Set.rangeFactorization q x) = x) ↔ Function.Injective q) ∧
        (∀ (T : Type w) (r : T → T → Prop),
          (¬ ∃ f : ℕ → T, ∀ n, r (f n) (f (n + 1))) →
            ∀ t : T, ¬ Relation.TransGen r t t)) ∧
  (
    (∀ {Y : Type} [Fintype Y] (P Q : FiniteLaw Y),
          0 < discrimination P.mass Q.mass →
            (∀ {A : Type} [Fintype A] (p : FiniteProtocol Bool A Y) (c : ℝ),
              PairMenu p (discrimination P.mass Q.mass) →
              ∀ (n : ℕ) (bank : List (List (A × Y))), HistoryBank n bank →
                c ≤ terminalMI p n bank →
                  c * Real.log 2 / discrimination P.mass Q.mass ≤ expectedCost p n bank) ∧
            (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
              1 - Real.binEntropy η / Real.log 2 ≤
                  terminalMI (repeatProtocol P Q N) N (historyBank Unit Y N) ∧
                expectedCost (repeatProtocol P Q N) N (historyBank Unit Y N) = N ∧
                (N : ℝ) ≤ 4 * Real.log (1 / (2 * η)) / discrimination P.mass Q.mass + 1)) ∧
        (∀ (ε : ℝ) (hε : |ε| ≤ 1 / 2), 0 < ε →
          readingDiscrimination (binaryRow ε hε) true false = 8 * ε ^ 2 ∧
          (∀ (A : Type) [Fintype A] (p : FiniteProtocol Bool A Bool) (c : ℝ),
            PairMenu p (8 * ε ^ 2) → ∀ n bank, HistoryBank n bank →
              c ≤ terminalMI p n bank → c * Real.log 2 ≤ 8 * ε ^ 2 * expectedCost p n bank) ∧
          (∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∃ N : ℕ,
            1 - Real.binEntropy η / Real.log 2 ≤
                terminalMI (repeatProtocol (binaryRow ε hε true) (binaryRow ε hε false) N) N
                  (historyBank Unit Bool N) ∧
              8 * ε ^ 2 * N ≤ 4 * Real.log (1 / (2 * η)) + 8 * ε ^ 2) ∧
          (∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
            (1 - Real.binEntropy η / Real.log 2) * Real.log 2 ≤
                8 * ε ^ 2 * leastRepeatCost (binaryRow ε hε true) (binaryRow ε hε false)
                  (1 - Real.binEntropy η / Real.log 2) ∧
              8 * ε ^ 2 * leastRepeatCost (binaryRow ε hε true) (binaryRow ε hε false)
                  (1 - Real.binEntropy η / Real.log 2) ≤
                4 * Real.log (1 / (2 * η)) + 8 * ε ^ 2))
  )

/-- All five quantified claims of the structural phase-transition dictionary
hold: observer symmetry, place orbits, merge entropy, irreversibility, and the
two-sided reading-cost pole in discrimination and positive binary bias. -/
theorem landauDictionary : LandauDictionaryGoal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Q q
    exact landau_symmetry_change q
  · intro X Q q n
    exact landau_order_parameter q n
  · refine ⟨?_, ?_⟩
    · intro X Q _ _ _ _ q
      exact landau_entropy_release q
    · intro X Q q C hC hconstant
      exact isolatedFiberUniformConditionalEntropy_bits q C hC hconstant
  · intro X Q q
    exact landau_irreversibility q
  · exact landau_reading_pole

end OperatorKO7.Meta.BoundaryObserver.LandauDictionary

