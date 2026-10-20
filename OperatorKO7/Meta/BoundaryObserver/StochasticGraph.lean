import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Stochastic observations and zero-error side records

Proof graph: Audit/ledgers/operational-inexpressibility/OBSERVATION-EXTENSIONS-PROOF-GRAPH.md,
nodes S1 and S2. Finite channels have nonnegative entries and normalized rows.
Decoder statements apply on positive support, for every input, without a prior.
No conclusion about an approximate decoder or a physical copying operation is inferred.
-/

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryObserver.StochasticGraph

structure Channel (X Y : Type*) [Fintype Y] where
  prob : X → Y → ℝ
  nonneg : ∀ x y, 0 ≤ prob x y
  row_sum : ∀ x, ∑ y, prob x y = 1

/-- A conflict is a common possible output from inputs with different targets. -/
def conflictGraph {X Y V : Type*} (K : X → Y → ℝ) (P : X → V) : SimpleGraph X where
  Adj x x' := P x ≠ P x' ∧ ∃ y, 0 < K x y ∧ 0 < K x' y
  symm := by
    rintro x x' ⟨h, y, hx, hx'⟩
    exact ⟨fun he => h he.symm, y, hx', hx⟩
  loopless := by
    intro x h
    exact h.1 rfl

/-- The decoder must return the target at every output with positive probability. -/
def Decodes {X Y V C : Type*} (K : X → Y → ℝ) (P : X → V)
    (side : X → C) (d : Y × C → V) : Prop :=
  ∀ x y, 0 < K x y → d (y, side x) = P x

/-- An unattained output receives an arbitrary target value; this is why V is nonempty. -/
theorem decoder_iff_coloring {X Y V C : Type*} [Nonempty V]
    (K : X → Y → ℝ) (P : X → V) (side : X → C) :
    (∃ d, Decodes K P side d) ↔
      ∀ ⦃x x'⦄, (conflictGraph K P).Adj x x' → side x ≠ side x' := by
  classical
  constructor
  · rintro ⟨d, hd⟩ x x' ⟨hP, y, hx, hx'⟩ hs
    exact hP ((hd x y hx).symm.trans (by simpa only [hs] using hd x' y hx'))
  · intro hcolor
    let d : Y × C → V := fun yc =>
      if h : ∃ x, 0 < K x yc.1 ∧ side x = yc.2 then P (Classical.choose h)
      else Classical.choice ‹Nonempty V›
    refine ⟨d, ?_⟩
    intro x y hx
    have hex : ∃ z, 0 < K z y ∧ side z = side x := ⟨x, hx, rfl⟩
    change (if h : ∃ z, 0 < K z y ∧ side z = side x then P (Classical.choose h)
      else Classical.choice ‹Nonempty V›) = P x
    rw [dif_pos hex]
    have hc := Classical.choose_spec hex
    by_contra hP
    exact (hcolor ⟨hP, y, hc.1, hx⟩) hc.2

/-- The least finite side alphabet is the chromatic number of the support-conflict graph. -/
theorem colorable_iff_decoder {X Y V : Type*} [Nonempty V]
    (K : X → Y → ℝ) (P : X → V) (n : ℕ) :
    (conflictGraph K P).Colorable n ↔
      ∃ side : X → Fin n, ∃ d, Decodes K P side d := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c, (decoder_iff_coloring K P c).mpr (fun {x x'} h => c.valid h)⟩
  · rintro ⟨side, hd⟩
    exact ⟨SimpleGraph.Coloring.mk side (fun {x x'} h => (decoder_iff_coloring K P side).mp hd h)⟩

theorem chromaticNumber_le_iff_decoder {X Y V : Type*} [Nonempty V]
    (K : X → Y → ℝ) (P : X → V) (n : ℕ) :
    (conflictGraph K P).chromaticNumber ≤ n ↔
      ∃ side : X → Fin n, ∃ d, Decodes K P side d := by
  rw [SimpleGraph.chromaticNumber_le_iff_colorable, colorable_iff_decoder]

noncomputable def deterministic {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (q : X → Y) : Channel X Y where
  prob x y := if q x = y then 1 else 0
  nonneg := by intro x y; split_ifs <;> norm_num
  row_sum := by intro x; simp

/-- The stochastic graph specializes to the deterministic observer-target graph. -/
theorem deterministic_graph {X Y V : Type*} [Fintype Y] [DecidableEq Y]
    (q : X → Y) (P : X → V) :
    conflictGraph (deterministic q).prob P =
      OperatorKO7.Meta.OperationalInexpressibility.Confusability.confusabilityGraph q P := by
  ext x x'
  change (P x ≠ P x' ∧ ∃ y, 0 < (if q x = y then (1 : ℝ) else 0) ∧
    0 < (if q x' = y then (1 : ℝ) else 0)) ↔ q x = q x' ∧ P x ≠ P x'
  constructor
  · rintro ⟨hp, y, hx, hx'⟩
    have hxq : q x = y := by by_contra h; simp [h] at hx
    have hxq' : q x' = y := by by_contra h; simp [h] at hx'
    exact ⟨hxq.trans hxq'.symm, hp⟩
  · rintro ⟨hq, hp⟩
    exact ⟨hp, q x, by simp, by simp [hq]⟩

/-- If every input can emit one common output, the side record must determine the whole target. -/
theorem common_output_decoder_iff {X Y V C : Type*} [Nonempty V]
    (K : X → Y → ℝ) (P : X → V) (side : X → C)
    (y : Y) (hy : ∀ x, 0 < K x y) :
    (∃ d, Decodes K P side d) ↔ ∀ x x', side x = side x' → P x = P x' := by
  rw [decoder_iff_coloring]
  constructor
  · intro h x x' hs
    by_contra hp
    exact (h ⟨hp, y, hy x, hy x'⟩) hs
  · intro h x x' he hs
    exact he.1 (h x x' hs)

/-- Product likelihood of N conditionally independent readings of the same input. -/
noncomputable def repeated {X Y : Type*} (K : X → Y → ℝ) (N : ℕ)
    (x : X) (ys : Fin N → Y) : ℝ := ∏ i, K x (ys i)

theorem repeated_pos {X Y : Type*} (K : X → Y → ℝ)
    (hK : ∀ x y, 0 < K x y) (N : ℕ) (x : X) (ys : Fin N → Y) :
    0 < repeated K N x ys := by
  exact Finset.prod_pos (fun i _ => hK x (ys i))

/-- Finite repetition of a full-support channel never removes the zero-error side requirement. -/
theorem full_support_repetition_decoder_iff {X Y V C : Type*} [Nonempty Y] [Nonempty V]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 < K x y)
    (P : X → V) (side : X → C) (N : ℕ) :
    (∃ d, Decodes (repeated K N) P side d) ↔
      ∀ x x', side x = side x' → P x = P x' := by
  classical
  exact common_output_decoder_iff (repeated K N) P side
    (fun _ => Classical.choice ‹Nonempty Y›) (fun x => repeated_pos K hK N x _)

/-- Positive finite repetition of a reading with nonnegative entries leaves its support-conflict
graph unchanged, with no full-support hypothesis: a word of positive weight under an input has
every letter of positive weight, and a common output repeated gives a common word. -/
theorem repeated_conflictGraph_eq {X Y V : Type*} (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (P : X → V) (N : ℕ) :
    conflictGraph (repeated K (N + 1)) P = conflictGraph K P := by
  have hfac : ∀ x (ys : Fin (N + 1) → Y), 0 < repeated K (N + 1) x ys → 0 < K x (ys 0) := by
    intro x ys h
    refine lt_of_le_of_ne (hK x (ys 0)) (fun h0 => h.ne' ?_)
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (N + 1))) h0.symm
  ext x x'
  constructor
  · rintro ⟨hP, ys, hx, hx'⟩
    exact ⟨hP, ys 0, hfac x ys hx, hfac x' ys hx'⟩
  · rintro ⟨hP, y, hx, hx'⟩
    exact ⟨hP, fun _ => y, Finset.prod_pos (fun _ _ => hx), Finset.prod_pos (fun _ _ => hx')⟩

/-- Every zero-error side-record criterion of a nonnegative reading is the same for one reading
and for any positive finite number of independent readings. -/
theorem repeated_decoder_iff {X Y V C : Type*} [Nonempty V]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 ≤ K x y) (P : X → V) (side : X → C) (N : ℕ) :
    (∃ d, Decodes (repeated K (N + 1)) P side d) ↔ (∃ d, Decodes K P side d) := by
  rw [decoder_iff_coloring, decoder_iff_coloring, repeated_conflictGraph_eq K hK P N]

/-- Zero readings: the one empty word has weight one under every input, so it is a common output
of every pair and the side record alone must determine the target. -/
theorem repeated_zero_decoder_iff {X Y V C : Type*} [Nonempty V]
    (K : X → Y → ℝ) (P : X → V) (side : X → C) :
    (∃ d, Decodes (repeated K 0) P side d) ↔ ∀ x x', side x = side x' → P x = P x' :=
  common_output_decoder_iff (repeated K 0) P side (fun i : Fin 0 => i.elim0)
    (fun x => by simp [repeated])

/-- Under full support and a nonempty output set, two inputs conflict exactly at distinct
targets; with `repeated_conflictGraph_eq`, this is the full-support proposition as a special case. -/
theorem full_support_conflictGraph_adj {X Y V : Type*} [Nonempty Y]
    (K : X → Y → ℝ) (hK : ∀ x y, 0 < K x y) (P : X → V) (x x' : X) :
    (conflictGraph K P).Adj x x' ↔ P x ≠ P x' :=
  ⟨fun h => h.1, fun h => ⟨h, Classical.choice ‹Nonempty Y›, hK _ _, hK _ _⟩⟩

/-- A five-cycle channel: input i emits edge i or the preceding edge with equal probabilities. -/
noncomputable def cycleChannel : Channel (Fin 5) (Fin 5) where
  prob x y := if x.val = y.val ∨ x.val = (y.val + 1) % 5 then 1 / 2 else 0
  nonneg := by intro x y; split_ifs <;> norm_num
  row_sum := by
    intro x
    fin_cases x <;> norm_num [Fin.sum_univ_succ]

def cycleAdjacent (x y : Fin 5) : Prop :=
  x ≠ y ∧ (x.val = (y.val + 1) % 5 ∨ y.val = (x.val + 1) % 5)

instance cycleAdjacentDecidable (x y : Fin 5) : Decidable (cycleAdjacent x y) := inferInstanceAs
  (Decidable (x ≠ y ∧ (x.val = (y.val + 1) % 5 ∨ y.val = (x.val + 1) % 5)))

theorem cycle_positive (x y : Fin 5) :
    0 < cycleChannel.prob x y ↔ x.val = y.val ∨ x.val = (y.val + 1) % 5 := by
  change (0 : ℝ) < (if x.val = y.val ∨ x.val = (y.val + 1) % 5 then 1 / 2 else 0) ↔ _
  split_ifs with h <;> simp_all

theorem cycle_graph (x y : Fin 5) :
    (conflictGraph cycleChannel.prob id).Adj x y ↔ cycleAdjacent x y := by
  change (x ≠ y ∧ ∃ z, 0 < cycleChannel.prob x z ∧ 0 < cycleChannel.prob y z) ↔ _
  simp only [cycle_positive]
  fin_cases x <;> fin_cases y <;> decide

/-- Every visible output is consistent with exactly two inputs. -/
theorem cycle_output_support (y : Fin 5) :
    (Finset.univ.filter (fun x : Fin 5 => 0 < cycleChannel.prob x y)).card = 2 := by
  classical
  simp_rw [cycle_positive]
  fin_cases y <;> decide

/-- No binary side record repairs the five-cycle channel. -/
theorem cycle_no_two_colors :
    ¬ ∃ c : Fin 5 → Fin 2, ∀ x y, cycleAdjacent x y → c x ≠ c y := by
  decide

/-- A three-symbol side record does repair the same channel. -/
theorem cycle_three_colors :
    ∃ c : Fin 5 → Fin 3, ∀ x y, cycleAdjacent x y → c x ≠ c y := by
  decide

theorem cycle_no_binary_decoder :
    ¬ ∃ side : Fin 5 → Fin 2, ∃ d, Decodes cycleChannel.prob id side d := by
  rintro ⟨s, hd⟩
  have hs := (decoder_iff_coloring cycleChannel.prob id s).mp hd
  exact cycle_no_two_colors ⟨s, fun x y h => hs ((cycle_graph x y).mpr h)⟩

theorem cycle_ternary_decoder :
    ∃ side : Fin 5 → Fin 3, ∃ d, Decodes cycleChannel.prob id side d := by
  obtain ⟨s, hs⟩ := cycle_three_colors
  exact ⟨s, (decoder_iff_coloring cycleChannel.prob id s).mpr
    (fun {x y} h => hs x y ((cycle_graph x y).mp h))⟩

/-- The independent product used above is itself a normalized channel, including N = 0. -/
noncomputable def repeatedChannel {X Y : Type*} [Fintype Y] (K : Channel X Y) (N : ℕ) :
    Channel X (Fin N → Y) where
  prob := repeated K.prob N
  nonneg := by
    intro x ys
    exact Finset.prod_nonneg (fun i _ => K.nonneg x (ys i))
  row_sum := by
    intro x
    change (∑ ys : Fin N → Y, ∏ i, K.prob x (ys i)) = 1
    rw [← Fintype.sum_pow (K.prob x) N, K.row_sum x, one_pow]

/-- The normalized product channel of `N + 1` readings has the support-conflict graph of one. -/
theorem repeatedChannel_conflictGraph_eq {X Y V : Type*} [Fintype Y]
    (K : Channel X Y) (P : X → V) (N : ℕ) :
    conflictGraph (repeatedChannel K (N + 1)).prob P = conflictGraph K.prob P :=
  repeated_conflictGraph_eq K.prob K.nonneg P N

open OperatorKO7.Meta.InformationalIncompleteness.ShannonFinite
open OperatorKO7.Meta.BoundaryObserver.BitDivision

/-- Mutual information in bits for the actual joint law of the hidden label and N readings. -/
noncomputable def readingsInformation (N : ℕ) (ε : ℝ) : ℝ :=
  (entropy (fun b : Bool => ∑ ys, readingsJoint N ε b ys) +
    entropy (fun ys : Fin N → Bool => ∑ b, readingsJoint N ε b ys) -
    entropy (fun z : Bool × (Fin N → Bool) => readingsJoint N ε z.1 z.2)) / Real.log 2

theorem readingsInformation_le_quadratic (N : ℕ) (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 2) : readingsInformation N ε ≤ 4 * N * ε ^ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hb := FourTestTables.one_sub_binEntropy_le_sq (2 * ε)
    (abs_le.mpr ⟨by linarith, by linarith⟩)
  have he : (1 + 2 * ε) / 2 = 1 / 2 + ε := by ring
  rw [he] at hb
  have hgap := mul_le_mul_of_nonneg_right hb hlog.le
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hlog.ne'] at hgap
  have hread := (readings_mutualInfo_le N ε h0 h1).trans (min_le_right _ _)
  unfold readingsInformation
  apply (div_le_iff₀ hlog).mpr
  calc
    _ ≤ N * (Real.log 2 - Real.binEntropy (1 / 2 + ε)) := hread
    _ ≤ N * ((2 * ε) ^ 2 * Real.log 2) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = (4 * N * ε ^ 2) * Real.log 2 := by ring

/-- A positive information target forces an inverse-square lower bound on the reading count. -/
theorem information_target_cost (N : ℕ) (ε c : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2)
    (hc : c ≤ readingsInformation N ε) : c / (4 * ε ^ 2) ≤ N := by
  apply (div_le_iff₀ (by positivity : 0 < 4 * ε ^ 2)).mpr
  have h := hc.trans (readingsInformation_le_quadratic N ε h0.le h1)
  nlinarith

/-- For every finite reading budget and positive information target, all sufficiently weak
signals fail the target. The neighborhood is explicit and does not presume a stopping policy. -/
theorem bounded_budget_fails_near_zero (B : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ η > 0, ∀ ε, 0 ≤ ε → ε < η → ∀ N ≤ B, readingsInformation N ε < c := by
  let η : ℝ := min (1 / 2) (c / (4 * (B + 1)))
  have hd : (0 : ℝ) < 4 * (B + 1) := by positivity
  refine ⟨η, lt_min (by norm_num) (div_pos hc hd), ?_⟩
  intro ε h0 hη N hN
  have hhalf : ε < 1 / 2 := hη.trans_le (min_le_left _ _)
  have hsmall : ε < c / (4 * (B + 1)) := hη.trans_le (min_le_right _ _)
  have hscaled := (lt_div_iff₀ hd).mp hsmall
  have hn : (N : ℝ) ≤ B := by exact_mod_cast hN
  have heps : ε ^ 2 ≤ ε := by nlinarith
  calc
    readingsInformation N ε ≤ 4 * N * ε ^ 2 :=
      readingsInformation_le_quadratic N ε h0 hhalf.le
    _ ≤ 4 * B * ε ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg ε)]
    _ ≤ 4 * B * ε := mul_le_mul_of_nonneg_left heps (by positivity)
    _ ≤ 4 * (B + 1) * ε := by nlinarith
    _ < c := by nlinarith

end OperatorKO7.Meta.BoundaryObserver.StochasticGraph
