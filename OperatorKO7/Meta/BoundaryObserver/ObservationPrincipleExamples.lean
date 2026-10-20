import OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest
import OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
import OperatorKO7.Meta.BoundaryObserver.DemandComplex
import OperatorKO7.Meta.BoundaryObserver.FairReadingBound
import OperatorKO7.Meta.BoundaryObserver.ErasureReading
import OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import OperatorKO7.Meta.BoundaryObserver.ObserverRealization
import OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction
import OperatorKO7.Meta.BoundaryObserver.PairResolution
import OperatorKO7.Meta.BoundaryObserver.GaussianTotals

set_option autoImplicit false

/-!
# The finite examples of the Boundary-Observation Principle

Each section proves the sentences of one example of the manuscript that no earlier declaration
states: the two occurrences of one content and their invisible group, the readout reading of the
three-demand obstruction and the uniqueness of each minimal obstruction, the conditional rows of
the one-time pad after its first report, the two ends `p = 1` and `p = 0` of the erasure reading,
the constant diagonal of the exclusive-or evaluation and the new code that represents it, the
angles, refused weights and comparison relation of the corner table, the assignments and the
common law of the triangle, the quadratic forms of the two phase states, and the two values of
the overlap coefficient of the repeated reading.

Relation: none; every statement concerns finite sets, finite sums or two-by-two matrices.
Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleExamples

open OperatorKO7.Meta.OperationalInexpressibility.LicenseStabilizer
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

/-! ## Example `ex:two-voids`: two occurrences of one content -/

/-- The occurrence at the frame place. -/
def occFrame : Occ Unit := ((), Role.frame)

/-- The occurrence at the active place. -/
def occActive : Occ Unit := ((), Role.active)

/-- Every occurrence of the one content is one of the two named occurrences. -/
theorem occ_cases (o : Occ Unit) : o = occFrame ∨ o = occActive := by
  rcases o with ⟨⟨⟩, r⟩
  cases r
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The two named occurrences are distinct. -/
theorem occFrame_ne_occActive : occFrame ≠ occActive := by
  intro h
  have := congrArg Prod.snd h
  exact Role.noConfusion this

/-- The places of the occurrence model, two of them, as the two Boolean values. -/
def roleEquivBool : Role ≃ Bool where
  toFun r := match r with
    | .frame => false
    | .active => true
  invFun b := if b then Role.active else Role.frame
  left_inv r := by cases r <;> rfl
  right_inv b := by cases b <;> rfl

/-- The occurrence set of one content and two places has two elements. -/
theorem occurrences_card : Nat.card (Occ Unit) = 2 := by
  rw [Nat.card_congr ((Equiv.prodCongr (Equiv.refl Unit) roleEquivBool).trans
    (Equiv.punitProd Bool))]
  simp

/-- The pairs of contents form a one-element set. -/
theorem content_pairs_card : Nat.card (Unit × Unit) = 1 := by
  simp

/-- The invisible group of the constant content observer is the whole permutation group. -/
theorem content_stabilizer_eq_top :
    licenseStabilizer (fun o : Occ Unit => o.1) = ⊤ := by
  ext σ
  constructor
  · intro _
    exact Subgroup.mem_top σ
  · intro _
    show ∀ x, (σ x).1 = x.1
    intro x
    exact Subsingleton.elim _ _

/-- Every permutation of the two occurrences is the identity or the transposition. -/
theorem perm_occurrences (σ : Equiv.Perm (Occ Unit)) :
    σ = 1 ∨ σ = Equiv.swap occFrame occActive := by
  rcases occ_cases (σ occFrame) with h | h
  · left
    have hb : σ occActive = occActive := by
      rcases occ_cases (σ occActive) with h' | h'
      · exact absurd (σ.injective (h'.trans h.symm)) occFrame_ne_occActive.symm
      · exact h'
    ext o : 1
    rcases occ_cases o with rfl | rfl
    · simp [h]
    · simp [hb]
  · right
    have hb : σ occActive = occFrame := by
      rcases occ_cases (σ occActive) with h' | h'
      · exact h'
      · exact absurd (σ.injective (h'.trans h.symm)) occFrame_ne_occActive.symm
    ext o : 1
    rcases occ_cases o with rfl | rfl
    · simp [h, Equiv.swap_apply_left]
    · simp [hb, Equiv.swap_apply_right]

/-- The invisible group of the content observer is exactly the identity and the transposition
of the two occurrences. -/
theorem content_stabilizer_two_elements (σ : Equiv.Perm (Occ Unit)) :
    σ ∈ licenseStabilizer (fun o : Occ Unit => o.1) ↔
      σ = 1 ∨ σ = Equiv.swap occFrame occActive := by
  rw [content_stabilizer_eq_top]
  exact ⟨fun _ => perm_occurrences σ, fun _ => Subgroup.mem_top σ⟩

/-- On the two occurrences the transposition sends the separating test of the frame occurrence
to its negation. -/
theorem swap_negates_separating_test (a : Occ Unit) :
    decide (Equiv.swap occFrame occActive a = occFrame) = !decide (a = occFrame) := by
  rcases occ_cases a with rfl | rfl
  · simp [Equiv.swap_apply_left, occFrame_ne_occActive.symm]
  · simp [Equiv.swap_apply_right, occFrame_ne_occActive.symm]

/-! ## Example `ex:demand-triple`: the three-demand obstruction -/

open UniversalObservation.Demand

/-- The permitted readout of index `w`: it fails, that is differs from zero, exactly at `w`. -/
def tripleReadout (w : Fin 3) : Fin 3 → Fin 2 := fun i => if i = w then 1 else 0

/-- The three permitted readouts of the readout contract. -/
def tripleReadouts : Set (Fin 3 → Fin 2) := Set.range tripleReadout

/-- Each permitted readout fails at exactly one input. -/
theorem tripleReadout_fails_once (w i : Fin 3) : tripleReadout w i ≠ 0 ↔ i = w := by
  unfold tripleReadout
  split_ifs with h <;> simp [h]

/-- The three-demand problem is the readout contract with the identity observer, the constant
zero target and the three permitted readouts: the two problems have the same successful sets. -/
theorem triple_readout_good_iff (D : Set (Fin 3)) :
    Good (readoutProblem id (fun _ => (0 : Fin 2)) tripleReadouts) D ↔ Good triple D := by
  constructor
  · rintro ⟨⟨f, w, rfl⟩, hf⟩
    refine ⟨w, fun i hi => ?_⟩
    have h := hf i hi
    change tripleReadout w i = 0 at h
    change w ≠ i
    intro hwi
    exact (tripleReadout_fails_once w i).2 hwi.symm h
  · rintro ⟨w, hw⟩
    refine ⟨⟨tripleReadout w, w, rfl⟩, fun i hi => ?_⟩
    change tripleReadout w i = 0
    by_contra h
    exact hw i hi ((tripleReadout_fails_once w i).1 h).symm

/-- A set of the three demands is successful exactly when it omits one demand. -/
theorem triple_good_iff (B : Set (Fin 3)) : Good triple B ↔ ∃ w, w ∉ B := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, fun hB => hw w hB rfl⟩
  · rintro ⟨w, hwB⟩
    exact ⟨w, fun i hi hwi => hwB (hwi ▸ hi)⟩

/-- The only minimal obstruction of the three-demand problem is the triple. -/
theorem triple_minimal_obstruction_unique (B : Finset (Fin 3)) :
    MinimalBad triple B ↔ B = Finset.univ := by
  constructor
  · rintro ⟨hbad, -⟩
    by_contra hne
    obtain ⟨w, hw⟩ : ∃ w, w ∉ B := by
      by_contra hall
      push_neg at hall
      exact hne (Finset.eq_univ_iff_forall.2 hall)
    exact hbad ((triple_good_iff _).2 ⟨w, by simpa using hw⟩)
  · rintro rfl
    exact triple_minimal_obstruction

/-- The one-demand problem whose satisfaction is always false. -/
def falseSingleton : Problem (Fin 1) (Fin 1) where
  sat _ _ := False

/-- With one demand, one candidate and satisfaction always false, the only minimal obstruction
is the singleton. -/
theorem falseSingleton_minimal_obstruction_unique (B : Finset (Fin 1)) :
    MinimalBad falseSingleton B ↔ B = Finset.univ := by
  have hgood : ∀ A : Finset (Fin 1), Good falseSingleton (A : Set (Fin 1)) ↔ A = ∅ := by
    intro A
    constructor
    · rintro ⟨x, hx⟩
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact hx i (by simpa using hi)
    · rintro rfl
      exact ⟨0, fun i hi => by simp at hi⟩
  have huniv : (Finset.univ : Finset (Fin 1)) ≠ ∅ := Finset.univ_nonempty.ne_empty
  constructor
  · rintro ⟨hbad, -⟩
    have hne : B ≠ ∅ := fun h => hbad ((hgood B).2 h)
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
    apply Finset.eq_univ_iff_forall.2
    intro j
    rwa [Subsingleton.elim j i]
  · rintro rfl
    refine ⟨fun h => huniv ((hgood _).1 h), fun A hA => (hgood A).2 ?_⟩
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
    apply hA.2
    intro j _
    rwa [Subsingleton.elim j i]

/-- With no candidate, the empty set is the only minimal obstruction. -/
theorem empty_candidates_minimal_obstruction_unique {I : Type*} (P : Problem I Empty)
    (B : Finset I) : MinimalBad P B ↔ B = ∅ := by
  constructor
  · rintro ⟨-, hmin⟩
    by_contra hne
    obtain ⟨x, -⟩ := hmin ∅ (Finset.nonempty_iff_ne_empty.2 hne).empty_ssubset
    exact x.elim
  · rintro rfl
    exact empty_candidates_empty_obstruction P

/-! ## Example `ex:conditional-rows`: equal marginals, different conditional rows -/

open OperatorKO7.Meta.BoundaryObserver.ProtocolResolution

/-- The joint law of the reports `Y₁ = K` and `Y₂ = K + b` under the label `b`, for a fair key
`K` independent of the label. -/
noncomputable def padReports (b : ZMod 2) (y : ZMod 2 × ZMod 2) : ℝ :=
  ∑ k : ZMod 2, (1 / 2 : ℝ) * (if y.1 = k ∧ y.2 = k + b then 1 else 0)

/-- In `ZMod 2` no element equals its successor. -/
theorem zmod_two_ne_add_one (k : ZMod 2) : k ≠ k + 1 := by
  revert k
  decide

/-- The two reports have joint mass one half on the pairs with `Y₂ = Y₁ + b` and zero elsewhere. -/
theorem padReports_eq (b : ZMod 2) (y : ZMod 2 × ZMod 2) :
    padReports b y = if y.2 = y.1 + b then 1 / 2 else 0 := by
  unfold padReports
  rw [Finset.sum_eq_single y.1]
  · by_cases h : y.2 = y.1 + b <;> simp [h]
  · intro k _ hk
    have hnot : ¬ (y.1 = k ∧ y.2 = k + b) := fun h => hk h.1.symm
    simp [hnot]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The first report is fair under either label. -/
theorem padReports_first_fair (b k : ZMod 2) : ∑ y₂, padReports b (k, y₂) = 1 / 2 := by
  simp only [padReports_eq]
  simp

/-- The second report is fair under either label. -/
theorem padReports_second_fair (b y₂ : ZMod 2) : ∑ y₁, padReports b (y₁, y₂) = 1 / 2 := by
  simp only [padReports_eq]
  have h : ∀ y₁ : ZMod 2, (y₂ = y₁ + b) ↔ (y₁ = y₂ - b) := fun y₁ => by
    rw [eq_sub_iff_add_eq, eq_comm]
  simp only [h]
  simp

/-- The label is the sum of the two reports on every pair of positive mass. -/
theorem padReports_label (b : ZMod 2) (y : ZMod 2 × ZMod 2) (h : padReports b y ≠ 0) :
    b = y.1 + y.2 := by
  rw [padReports_eq] at h
  split_ifs at h with hy
  · rw [hy, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · exact absurd rfl h

/-- The conditional row of the second report after the first report `k`, under the label `b`. -/
noncomputable def secondRow (b k y₂ : ZMod 2) : ℝ :=
  padReports b (k, y₂) / ∑ y, padReports b (k, y)

/-- After the first report `k`, the second report is the point mass at `k + b`. -/
theorem secondRow_eq (b k y₂ : ZMod 2) : secondRow b k y₂ = if y₂ = k + b then 1 else 0 := by
  unfold secondRow
  rw [padReports_first_fair, padReports_eq]
  split_ifs <;> norm_num

/-- After the first report the second report has different conditional rows under the two
labels. -/
theorem secondRow_differ (k : ZMod 2) : secondRow 0 k ≠ secondRow 1 k := by
  intro h
  have h1 := congrFun h k
  rw [secondRow_eq, secondRow_eq] at h1
  simp [zmod_two_ne_add_one k] at h1

/-- Under the fair label, the second report after the first report `k` carries one bit, so the
local information of the second reading is positive at every first report. -/
theorem second_reading_information (k : ZMod 2) :
    jointMI (fun by_ : Bool × ZMod 2 =>
        binaryPrior (1 / 2) by_.1 * secondRow (if by_.1 then 1 else 0) k by_.2) = 1 := by
  have hrow : (fun by_ : Bool × ZMod 2 =>
        binaryPrior (1 / 2) by_.1 * secondRow (if by_.1 then 1 else 0) k by_.2) =
      (fun by_ : Bool × ZMod 2 => binaryPrior (1 / 2) by_.1 *
        (if by_.2 = (if by_.1 then k + 1 else k + 0) then 1 else 0)) := by
    funext by_
    rcases by_ with ⟨b, y₂⟩
    rw [secondRow_eq]
    cases b <;> simp
  rw [hrow]
  have hne : k + 1 ≠ k + 0 := by
    rw [add_zero]
    exact (zmod_two_ne_add_one k).symm
  exact (FairReadingBound.fair_bound_attained_split (k + 1) (k + 0) hne).1

/-- The local zero-capacity hypothesis fails for the second reading: its local information
exceeds `κ c` for `κ = 0` and every cost `c`, although the unconditional report laws agree under
the two labels. -/
theorem conditional_rows_capacity_fails (k : ZMod 2) (c : ℝ) :
    (∀ b b' k' : ZMod 2, ∑ y₂, padReports b (k', y₂) = ∑ y₂, padReports b' (k', y₂)) ∧
      ¬ jointMI (fun by_ : Bool × ZMod 2 =>
        binaryPrior (1 / 2) by_.1 * secondRow (if by_.1 then 1 else 0) k by_.2) ≤ 0 * c := by
  refine ⟨fun b b' k' => by rw [padReports_first_fair, padReports_first_fair], ?_⟩
  rw [second_reading_information, zero_mul]
  norm_num

/-! ## Example `ex:erasure`: the two ends of the erasure reading -/

open OperatorKO7.Meta.BoundaryObserver.ErasureReading
open OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

/-- At `p = 1` one reading suffices: the rows have disjoint supports, discrimination two, and a
decoder that is correct at every output of positive probability. -/
theorem erasure_one_reading_suffices :
    discrimination (erasureRow 1 true) (erasureRow 1 false) = 2 ∧
      (∀ y, erasureRow 1 true y * erasureRow 1 false y = 0) ∧
      ∃ dec : Option Bool → Bool, ∀ z y, erasureRow 1 z y ≠ 0 → dec y = z := by
  refine ⟨?_, ?_, ⟨fun y => y.getD false, ?_⟩⟩
  · rw [erasure_discrimination_eq_two_mul 1 one_pos, mul_one]
  · intro y
    rcases y with _ | _ | _ <;> simp [erasureRow]
  · intro z y hy
    rcases y with _ | b
    · simp [erasureRow] at hy
    · simp only [erasureRow] at hy
      split_ifs at hy with hb
      · simp [hb]
      · exact absurd rfl hy

/-- The `N`-fold row of the erasure reading. -/
noncomputable def erasureWord (p : ℝ) (N : ℕ) (z : Bool) (w : Fin N → Option Bool) : ℝ :=
  ∏ i, erasureRow p z (w i)

/-- The `N`-fold rows of one probability row sum to one. -/
theorem erasureWord_sum (p : ℝ) (N : ℕ) (z : Bool) :
    ∑ w, erasureWord p N z w = 1 := by
  unfold erasureWord
  rw [← Fintype.prod_sum (fun (_ : Fin N) (y : Option Bool) => erasureRow p z y)]
  apply Finset.prod_eq_one
  intro i _
  rw [Fintype.sum_option]
  cases z <;> simp [erasureRow]

/-- At `p = 0` every reading has equal rows under the two labels, the rows of every number of
readings agree, the discrimination is zero, and the fair label acquires no information at any
number of readings. -/
theorem erasure_zero_no_information :
    erasureRow 0 true = erasureRow 0 false ∧
      discrimination (erasureRow 0 true) (erasureRow 0 false) = 0 ∧
      ∀ N : ℕ, erasureWord 0 N true = erasureWord 0 N false ∧
        jointMI (fun bw : Bool × (Fin N → Option Bool) =>
          binaryPrior (1 / 2) bw.1 * erasureWord 0 N bw.1 bw.2) = 0 := by
  have hrow : erasureRow 0 true = erasureRow 0 false := by
    funext y
    rcases y with _ | b <;> simp [erasureRow]
  refine ⟨hrow, ?_, fun N => ?_⟩
  · rw [hrow]
    unfold discrimination
    simp
  · have hword : erasureWord 0 N true = erasureWord 0 N false := by
      funext w
      simp [erasureWord, hrow]
    refine ⟨hword, ?_⟩
    have hconst : (fun bw : Bool × (Fin N → Option Bool) =>
        binaryPrior (1 / 2) bw.1 * erasureWord 0 N bw.1 bw.2) =
        (fun bw : Bool × (Fin N → Option Bool) =>
          binaryPrior (1 / 2) bw.1 * erasureWord 0 N false bw.2) := by
      funext bw
      rcases bw with ⟨b, w⟩
      cases b
      · rfl
      · rw [hword]
    rw [hconst]
    apply jointMI_product_zero
    · rw [Fintype.sum_bool]
      simp [binaryPrior]
    · exact erasureWord_sum 0 N false

/-! ## Example `ex:xor`: the constant diagonal and the new code -/

open OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds
open OperatorKO7.Meta.BoundaryObserver.DiagonalObservation

/-- The diagonal of the exclusive-or evaluation is the constant zero. -/
theorem xorEval_diagonal_const (c : Bool) : xorEval c c = false := by
  cases c <;> rfl

/-- The evaluation with one new code `none`, whose function is the constant zero; the old codes
keep their functions. -/
def xorExtended : Option Bool → Bool → Bool := fun c x => c.elim false (fun c => xorEval c x)

/-- A new code repairs the missing function: with the code `none` added, the diagonal of the
exclusive-or evaluation is represented, and every old code keeps its function. -/
theorem xor_new_code_repairs :
    Represented xorExtended (fun c => xorEval c c) ∧
      ∀ c x, xorExtended (some c) x = xorEval c x := by
  refine ⟨⟨none, ?_⟩, fun _ _ => rfl⟩
  funext x
  exact (xorEval_diagonal_const x).symm

/-! ## Example `ex:no-vectors`: the corner table -/

open OperatorKO7.Meta.BoundaryObserver.FourTestTables

/-- The angles of the corner table are `0, 0, 0, π`, with `π` at the pair `(1, 1)`. -/
theorem cornerTable_angles (x y : Bool) :
    Real.arccos (corr cornerTable x y) = if x && y then Real.pi else 0 := by
  cases x <;> cases y <;> simp [corr, cornerTable]; norm_num

/-- The angles of the corner table violate the cycle inequality with bound `π` at the pair
`(1, 1)`: the angle there exceeds the sum of the three others. -/
theorem cornerTable_angle_cycle_fails :
    ¬ (Real.arccos (corr cornerTable true true) ≤
        (Real.arccos (corr cornerTable false false) + Real.arccos (corr cornerTable false true) +
          Real.arccos (corr cornerTable true false) + Real.arccos (corr cornerTable true true)) -
          Real.arccos (corr cornerTable true true)) := by
  have h00 : Real.arccos (corr cornerTable false false) = 0 := by
    simpa using cornerTable_angles false false
  have h01 : Real.arccos (corr cornerTable false true) = 0 := by
    simpa using cornerTable_angles false true
  have h10 : Real.arccos (corr cornerTable true false) = 0 := by
    simpa using cornerTable_angles true false
  have h11 : Real.arccos (corr cornerTable true true) = Real.pi := by
    simpa using cornerTable_angles true true
  rw [h00, h01, h10, h11]
  intro h
  linarith [Real.pi_pos]

/-- The refused weights of the corner table are both zero. -/
theorem cornerTable_refused : refused0 cornerTable = 0 ∧ refused1 cornerTable = 0 := by
  constructor <;> simp [refused0, refused1, cornerTable]

/-- The totals of the corner table have no observer. -/
theorem cornerTable_not_observer : ¬ HasObserver cornerTable :=
  fun h => cornerTable_not_vectors (observer_hasVectors h)

/-- The agreement of single tests of the corner table: `inl x` is the test `aₓ`, `inr y` the
test `b_y`; two tests of one side agree when they are equal, and `aₓ` agrees with `b_y` when the
table has disagreement rate zero at `(x, y)`. -/
def cornerAgree : Bool ⊕ Bool → Bool ⊕ Bool → Prop
  | .inl x, .inl x' => x = x'
  | .inr y, .inr y' => y = y'
  | .inl x, .inr y => cornerTable x y = 0
  | .inr y, .inl x => cornerTable x y = 0

/-- The agreement relation of the corner table is reflexive. -/
theorem cornerAgree_refl (s : Bool ⊕ Bool) : cornerAgree s s := by
  rcases s with x | y <;> rfl

/-- The agreement relation of the corner table is symmetric. -/
theorem cornerAgree_symm (s t : Bool ⊕ Bool) : cornerAgree s t → cornerAgree t s := by
  rcases s with x | y <;> rcases t with x' | y' <;> intro h <;> simp only [cornerAgree] at h ⊢
  · exact h.symm
  · exact h
  · exact h
  · exact h.symm

/-- The chain of the example: `a₁` agrees with `b₀`, `b₀` with `a₀`, and `a₀` with `b₁`, while
`a₁` disagrees with `b₁`. -/
theorem cornerAgree_chain :
    cornerAgree (.inl true) (.inr false) ∧ cornerAgree (.inr false) (.inl false) ∧
      cornerAgree (.inl false) (.inr true) ∧ ¬ cornerAgree (.inl true) (.inr true) := by
  simp [cornerAgree, cornerTable]

/-- The agreement relation of the corner table is not transitive. -/
theorem cornerAgree_not_transitive :
    ¬ ∀ s t u, cornerAgree s t → cornerAgree t u → cornerAgree s u := by
  intro htrans
  obtain ⟨h1, h2, h3, h4⟩ := cornerAgree_chain
  exact h4 (htrans _ _ _ (htrans _ _ _ h1 h2) h3)

/-! ## Example `ex:triangle-repair`: the triangle -/

open OperatorKO7.Meta.BoundaryObserver.ObserverRealization

/-- The assignments `(1, 1, 0)`, `(0, 1, 1)` and `(1, 0, 1)` make two pairs disagree, and the pair
each leaves in agreement differs between the three: the first, second and third pair. -/
theorem triangle_named_assignments :
    triangleReport (true, true, false) = ![0, 1, 1] ∧
      triangleReport (false, true, true) = ![1, 0, 1] ∧
      triangleReport (true, false, true) = ![1, 1, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext j <;> fin_cases j <;> simp [triangleReport]

/-- The common law giving probability one third to each of `(1, 0, 0)`, `(0, 1, 0)` and
`(0, 0, 1)`. -/
noncomputable def oneHotLaw (a : Bool × Bool × Bool) : ℝ :=
  if a = (true, false, false) ∨ a = (false, true, false) ∨ a = (false, false, true) then 1 / 3
  else 0

/-- The law of the three one-hot assignments is a probability law whose disagreement rates are
two thirds at each pair, so it realizes the repaired rates. -/
theorem oneHotLaw_rates :
    (∀ a, 0 ≤ oneHotLaw a) ∧ ∑ a, oneHotLaw a = 1 ∧
      ∑ a, oneHotLaw a • triangleReport a = fun _ => (2 : ℝ) / 3 := by
  refine ⟨fun a => by unfold oneHotLaw; split_ifs <;> norm_num, ?_, ?_⟩
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, oneHotLaw]
    norm_num
  · funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      Fintype.sum_bool, oneHotLaw]
    fin_cases j <;> simp [triangleReport] <;> norm_num

/-! ## Example `ex:phase-reconstruction`: the forms of the two phase states -/

open OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction

/-- The forms of the two phase states are `|v₀ + v₁|² / 2` and `|v₀ - v₁|² / 2`. -/
theorem phaseMatrix_form_normSq (b : Bool) (v : Fin 2 → ℂ) :
    (form (phaseMatrix b) v v).re = Complex.normSq (v 0 + (if b then v 1 else -v 1)) / 2 := by
  rw [phaseMatrix_form, Complex.normSq_apply]
  cases b <;> simp <;> ring

/-! ## Definition `def:repeated-reading`: the two values of the overlap coefficient -/

open OperatorKO7.Meta.BoundaryObserver.PairResolution

/-- The overlap coefficient of a probability row with itself is one. -/
theorem bhattacharyya_self {Y : Type} [Fintype Y] (P : Y → ℝ) (hP : ∀ y, 0 ≤ P y)
    (h1 : ∑ y, P y = 1) : bhattacharyya P P = 1 := by
  unfold bhattacharyya
  rw [← h1]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.sqrt_mul_self (hP y)]

/-- The overlap coefficient of two rows with disjoint supports is zero. -/
theorem bhattacharyya_disjoint {Y : Type} [Fintype Y] (P Q : Y → ℝ)
    (h : ∀ y, P y * Q y = 0) : bhattacharyya P Q = 0 := by
  unfold bhattacharyya
  apply Finset.sum_eq_zero
  intro y _
  rw [h y, Real.sqrt_zero]

/-! ## Definition `def:table`(iii): vectors in any real inner-product space -/

/-- Definition `def:table`(iii) for an arbitrary real inner-product space: four unit vectors of any
real inner-product space whose inner products are the correlations give four unit vectors of a
finite Euclidean space with the same inner products, the span of the four vectors carried by an
orthonormal basis. The definition `HasVectors` therefore loses no table of the paper. -/
theorem hasVectors_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (d : FourTestTables.Table) (u v : Bool → E) (hu : ∀ x, ‖u x‖ = 1) (hv : ∀ y, ‖v y‖ = 1)
    (h : ∀ x y, @inner ℝ _ _ (u x) (v y) = FourTestTables.corr d x y) :
    FourTestTables.HasVectors d := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range u ∪ Set.range v)
  haveI : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Set.finite_range u).union (Set.finite_range v))
  have hmu : ∀ x, u x ∈ S := fun x => Submodule.subset_span (Or.inl ⟨x, rfl⟩)
  have hmv : ∀ y, v y ∈ S := fun y => Submodule.subset_span (Or.inr ⟨y, rfl⟩)
  let e := (stdOrthonormalBasis ℝ S).repr
  refine ⟨Module.finrank ℝ S, fun x => e ⟨u x, hmu x⟩, fun y => e ⟨v y, hmv y⟩,
    fun x => ?_, fun y => ?_, fun x y => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact hu x
  · rw [LinearIsometryEquiv.norm_map]
    exact hv y
  · rw [LinearIsometryEquiv.inner_map_map]
    exact h x y

/-- Definition `def:table`(iii): a table has unit vectors of a finite Euclidean space with the
correlations as inner products iff it has such vectors in some real inner-product space. -/
theorem hasVectors_iff_inner (d : FourTestTables.Table) :
    FourTestTables.HasVectors d ↔
      ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (u v : Bool → E),
        (∀ x, ‖u x‖ = 1) ∧ (∀ y, ‖v y‖ = 1) ∧
          ∀ x y, @inner ℝ _ _ (u x) (v y) = FourTestTables.corr d x y := by
  constructor
  · rintro ⟨n, u, v, hu, hv, h⟩
    exact ⟨EuclideanSpace ℝ (Fin n), inferInstance, inferInstance, u, v, hu, hv, h⟩
  · rintro ⟨E, _, _, u, v, hu, hv, h⟩
    exact hasVectors_of_inner d u v hu hv h

/-! ## Theorem `thm:vector-tables`(iii), the kept-refused form; Example `ex:no-vectors`, the totals -/

/-- Theorem `thm:vector-tables`(iii), the second form: a table with vectors has
`κ₀ρ₀ + κ₁ρ₁ ≥ 1/4`, with `κ_x = 1 - ρ_x` the kept weight of the test `x`. -/
theorem vectors_kept_refused_ge {d : FourTestTables.Table} (h : FourTestTables.HasVectors d) :
    1 / 4 ≤ (1 - FourTestTables.refused0 d) * FourTestTables.refused0 d +
      (1 - FourTestTables.refused1 d) * FourTestTables.refused1 d := by
  have hq := FourTestTables.vectors_quadratic h
  nlinarith [hq]

/-- Example `ex:no-vectors`, the totals: no law on `ℝ⁴` has the centred normal pair laws of the
correlations of the box as its marginals, so the totals of the box have no observer. -/
theorem cornerTable_totals_no_observer :
    ¬ GaussianTotals.HasPairMarginals FourTestTables.cornerTable := by
  intro h
  have hd : ∀ x y, 0 ≤ FourTestTables.cornerTable x y ∧ FourTestTables.cornerTable x y ≤ 1 := by
    intro x y
    cases x <;> cases y <;> simp [FourTestTables.cornerTable]
  exact FourTestTables.cornerTable_not_vectors
    ((GaussianTotals.hasVectors_iff_pairMarginals _ hd).2 h)

end OperatorKO7.Meta.BoundaryObserver.ObservationPrincipleExamples
