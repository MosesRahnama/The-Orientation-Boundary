import OperatorKO7.Meta.BoundaryObserver.InstrumentLoss
import OperatorKO7.Meta.BoundaryObserver.StochasticGraph

/-!
# Adaptive composition of finite stochastic instruments

The second operation may depend on the first recorded outcome. Both outcomes are
retained, while the intermediate state is summed out. The kernels have finite outcome and
post-state types; the initial state type may be infinite. Restoration is required at every
positive-probability joint output, without a prior on initial states.
-/

set_option autoImplicit false
open scoped BigOperators

namespace OperatorKO7.Meta.BoundaryObserver.InstrumentComposition

open InstrumentLoss

/-- Treat the outcome and post-state together as one stochastic observation. -/
noncomputable def jointChannel {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) : StochasticGraph.Channel X (Y × Z) where
  prob x yz := I.weight x yz.1 yz.2
  nonneg x yz := I.nonneg x yz.1 yz.2
  row_sum x := by
    rw [Fintype.sum_prod_type]
    exact I.total x

/-- Every normalized instrument has a possible joint output from each initial state. -/
theorem exists_joint_output {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : StochasticInstrument X Y Z) (x : X) : ∃ y z, 0 < I.weight x y z := by
  have h : 0 < ∑ y, ∑ z, I.weight x y z := by rw [I.total]; norm_num
  obtain ⟨y, _, hy⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun y _ => Finset.sum_nonneg (fun z _ => I.nonneg x y z))).mp h
  obtain ⟨z, _, hz⟩ := (Finset.sum_pos_iff_of_nonneg (fun z _ => I.nonneg x y z)).mp hy
  exact ⟨y, z, hz⟩

/-- The coloring theorem applied to joint outputs gives the restoration criterion. -/
theorem recoverable_iff_support_separated {X Y Z : Type*} [Nonempty X]
    [Fintype Y] [Fintype Z] (I : StochasticInstrument X Y Z) :
    StochasticRecoverable I ↔
      ∀ x x' y z, 0 < I.weight x y z → 0 < I.weight x' y z → x = x' := by
  constructor
  · rintro ⟨r, hr⟩ x x' y z hx hx'
    exact (hr x y z hx).symm.trans (hr x' y z hx')
  · intro hsep
    have hcolor : ∀ {x x'}, (StochasticGraph.conflictGraph (jointChannel I).prob id).Adj x x' →
        (fun _ : X => ()) x ≠ (fun _ : X => ()) x' := by
      rintro x x' ⟨hne, yz, hx, hx'⟩
      exact False.elim (hne (hsep x x' yz.1 yz.2 hx hx'))
    obtain ⟨d, hd⟩ := (StochasticGraph.decoder_iff_coloring
      (jointChannel I).prob id (fun _ : X => ())).mpr (fun {x x'} h => @hcolor x x' h)
    exact ⟨fun yz => d (yz, ()), fun x y z hx => hd x (y, z) hx⟩

/-- Adaptive composition retains both recorded outcomes and sums over the intermediate state. -/
noncomputable def sequential {X Y Z W T : Type*} [Fintype Y] [Fintype Z]
    [Fintype W] [Fintype T] (I : StochasticInstrument X Y Z)
    (J : Y → StochasticInstrument Z W T) : StochasticInstrument X (Y × W) T where
  weight x yw t := ∑ z, I.weight x yw.1 z * (J yw.1).weight z yw.2 t
  nonneg x yw t := Finset.sum_nonneg
    (fun z _ => mul_nonneg (I.nonneg x yw.1 z) ((J yw.1).nonneg z yw.2 t))
  total x := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ y, ∑ w, ∑ t, ∑ z, I.weight x y z * (J y).weight z w t) =
          ∑ y, ∑ z, I.weight x y z * (∑ w, ∑ t, (J y).weight z w t) := by
        apply Finset.sum_congr rfl
        intro y _
        calc
          _ = ∑ w, ∑ z, ∑ t, I.weight x y z * (J y).weight z w t := by
            apply Finset.sum_congr rfl
            intro w _
            exact Finset.sum_comm
          _ = ∑ z, ∑ w, ∑ t, I.weight x y z * (J y).weight z w t := Finset.sum_comm
          _ = _ := by simp only [Finset.mul_sum]
      _ = ∑ y, ∑ z, I.weight x y z := by simp only [(J _).total, mul_one]
      _ = 1 := I.total x

/-- Positive support is the relational composition of the two joint supports. -/
theorem sequential_positive_iff {X Y Z W T : Type*} [Fintype Y] [Fintype Z]
    [Fintype W] [Fintype T] (I : StochasticInstrument X Y Z)
    (J : Y → StochasticInstrument Z W T) (x : X) (y : Y) (w : W) (t : T) :
    0 < (sequential I J).weight x (y, w) t ↔
      ∃ z, 0 < I.weight x y z ∧ 0 < (J y).weight z w t := by
  change 0 < (∑ z, I.weight x y z * (J y).weight z w t) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg
    (fun z _ => mul_nonneg (I.nonneg x y z) ((J y).nonneg z w t))]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z, hz⟩
    rcases mul_pos_iff.mp hz with hp | hn
    · exact ⟨z, hp⟩
    · exact False.elim ((not_lt_of_ge (I.nonneg x y z)) hn.1)
  · rintro ⟨z, hi, hj⟩
    exact ⟨z, mul_pos hi hj⟩

/-- The second operation cannot change the distribution of an already retained first outcome. -/
theorem first_outcome_kept {X Y Z W T : Type*} [Fintype Y] [Fintype Z]
    [Fintype W] [Fintype T] (I : StochasticInstrument X Y Z)
    (J : Y → StochasticInstrument Z W T) (x : X) (y : Y) :
    (∑ w, outcomeLaw (sequential I J) x (y, w)) = outcomeLaw I x y := by
  change (∑ w, ∑ t, ∑ z, I.weight x y z * (J y).weight z w t) = ∑ z, I.weight x y z
  calc
    _ = ∑ w, ∑ z, ∑ t, I.weight x y z * (J y).weight z w t := by
      apply Finset.sum_congr rfl
      intro w _
      exact Finset.sum_comm
    _ = ∑ z, ∑ w, ∑ t, I.weight x y z * (J y).weight z w t := Finset.sum_comm
    _ = ∑ z, I.weight x y z * (∑ w, ∑ t, (J y).weight z w t) := by
      simp only [Finset.mul_sum]
    _ = _ := by simp only [(J y).total, mul_one]

/-- Equal joint laws before the continuation remain equal after any adaptive continuation. -/
theorem equal_joint_laws_persist {X Y Z W T : Type*} [Fintype Y] [Fintype Z]
    [Fintype W] [Fintype T] (I : StochasticInstrument X Y Z)
    (J : Y → StochasticInstrument Z W T) {x x' : X}
    (h : ∀ y z, I.weight x y z = I.weight x' y z) :
    ∀ yw t, (sequential I J).weight x yw t = (sequential I J).weight x' yw t := by
  intro yw t
  simp only [sequential, h]

/-- Restoration composes even when the second restoring instrument depends on the first outcome. -/
theorem sequential_recoverable {X Y Z W T : Type*} [Fintype Y] [Fintype Z]
    [Fintype W] [Fintype T] (I : StochasticInstrument X Y Z)
    (J : Y → StochasticInstrument Z W T) (hI : StochasticRecoverable I)
    (hJ : ∀ y, StochasticRecoverable (J y)) : StochasticRecoverable (sequential I J) := by
  classical
  obtain ⟨rI, hrI⟩ := hI
  choose rJ hrJ using hJ
  refine ⟨fun out => rI (out.1.1, rJ out.1.1 (out.1.2, out.2)), ?_⟩
  rintro x ⟨y, w⟩ t hp
  obtain ⟨z, hi, hj⟩ := (sequential_positive_iff I J x y w t).mp hp
  change rI (y, rJ y (w, t)) = x
  rw [hrJ y z w t hj]
  exact hrI x y z hi

/-- A normalized continuation cannot restore an input distinction already lost by the first joint support. -/
theorem first_recoverable_of_sequential {X Y Z W T : Type*} [Nonempty X]
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (h : StochasticRecoverable (sequential I J)) : StochasticRecoverable I := by
  apply (recoverable_iff_support_separated I).mpr
  intro x x' y z hi hi'
  obtain ⟨w, t, hj⟩ := exists_joint_output (J y) z
  exact (recoverable_iff_support_separated (sequential I J)).mp h x x' (y, w) t
    ((sequential_positive_iff I J x y w t).mpr ⟨z, hi, hj⟩)
    ((sequential_positive_iff I J x' y w t).mpr ⟨z, hi', hj⟩)

/-- With restoring continuations, all restoration failures are already failures of the first instrument. -/
theorem sequential_recoverable_iff {X Y Z W T : Type*} [Nonempty X]
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (hJ : ∀ y, StochasticRecoverable (J y)) :
    StochasticRecoverable (sequential I J) ↔ StochasticRecoverable I :=
  ⟨first_recoverable_of_sequential I J, fun hI => sequential_recoverable I J hI hJ⟩

/-- Reassociation of the retained outcomes commutes with three adaptive operations. -/
theorem sequential_associative {X Y Z W T U V : Type*}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T] [Fintype U] [Fintype V]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (K : Y × W → StochasticInstrument T U V) (x : X) (y : Y) (w : W) (u : U) (v : V) :
    (sequential (sequential I J) K).weight x ((y, w), u) v =
      (sequential I (fun y => sequential (J y) (fun w => K (y, w)))).weight x (y, (w, u)) v := by
  change (∑ t, (∑ z, I.weight x y z * (J y).weight z w t) * (K (y, w)).weight t u v) =
    ∑ z, I.weight x y z * (∑ t, (J y).weight z w t * (K (y, w)).weight t u v)
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A deterministic instrument is represented by a normalized joint point mass. -/
noncomputable def deterministic {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : Instrument X Y Z) : StochasticInstrument X Y Z := by
  classical
  exact {
    weight := fun x y z => if I.read x = y ∧ I.post x = z then 1 else 0
    nonneg := by intro x y z; split_ifs <;> norm_num
    total := by intro x; simp [ite_and]
  }

/-- Adaptive deterministic composition has the same recorded data as its stochastic representation. -/
def adaptiveDeterministic {X Y Z W T : Type*} (I : Instrument X Y Z)
    (J : Y → Instrument Z W T) : Instrument X (Y × W) T where
  read x := (I.read x, (J (I.read x)).read (I.post x))
  post x := (J (I.read x)).post (I.post x)

theorem deterministic_restoration_iff {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (I : Instrument X Y Z) : StochasticRecoverable (deterministic I) ↔ Recoverable I := by
  classical
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, fun x => hr x (I.read x) (I.post x) (by simp [deterministic])⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    intro x y z hp
    have he : I.read x = y ∧ I.post x = z := by
      by_contra hn
      simp [deterministic, hn] at hp
    simpa only [joint, he.1, he.2] using hr x

/-- Embedding a composite equals composing the embedded kernels, including the adaptive choice. -/
theorem deterministic_composition_commutes {X Y Z W T : Type*}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : Instrument X Y Z) (J : Y → Instrument Z W T) (x : X) (y : Y) (w : W) (t : T) :
    (sequential (deterministic I) (fun y => deterministic (J y))).weight x (y, w) t =
      (deterministic (adaptiveDeterministic I J)).weight x (y, w) t := by
  classical
  by_cases hy : I.read x = y
  · subst y
    change (∑ z, (if I.read x = I.read x ∧ I.post x = z then (1 : ℝ) else 0) *
      (if (J (I.read x)).read z = w ∧ (J (I.read x)).post z = t then 1 else 0)) = _
    rw [Finset.sum_eq_single (I.post x)]
    · simp [deterministic, adaptiveDeterministic]
    · intro z _ hz
      have hne : I.post x ≠ z := Ne.symm hz
      simp [hne]
    · simp
  · simp [sequential, deterministic, adaptiveDeterministic, ite_and, hy]

/-! ## Target-relative side information under continuation -/

/-- Every target conflict already present in the first joint support survives any normalized
adaptive continuation. The continuation sees only the retained outcome and post-state. -/
theorem sequential_conflict_persists {X Y Z W T V : Type*}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T) (P : X → V)
    {x x' : X} (h : (StochasticGraph.conflictGraph (jointChannel I).prob P).Adj x x') :
    (StochasticGraph.conflictGraph (jointChannel (sequential I J)).prob P).Adj x x' := by
  obtain ⟨hP, ⟨y, z⟩, hi, hi'⟩ := h
  obtain ⟨w, t, hj⟩ := exists_joint_output (J y) z
  exact ⟨hP, ((y, w), t),
    (sequential_positive_iff I J x y w t).mpr ⟨z, hi, hj⟩,
    (sequential_positive_iff I J x' y w t).mpr ⟨z, hi', hj⟩⟩

/-- If a side record permits exact decoding after continuation, it already permitted exact
decoding before it. Post-processing cannot create a missing target distinction. -/
theorem side_decoder_before_of_after {X Y Z W T V C : Type*} [Nonempty V]
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (side : X → C)
    (h : ∃ d, StochasticGraph.Decodes (jointChannel (sequential I J)).prob P side d) :
    ∃ d, StochasticGraph.Decodes (jointChannel I).prob P side d := by
  apply (StochasticGraph.decoder_iff_coloring (jointChannel I).prob P side).mpr
  intro x x' hconflict
  exact (StochasticGraph.decoder_iff_coloring
    (jointChannel (sequential I J)).prob P side).mp h
      (sequential_conflict_persists I J P hconflict)

/-- Every achievable finite side-alphabet budget after continuation was achievable before it.
This statement also covers an infinite input carrier and zero available side symbols. -/
theorem side_budget_before_of_after {X Y Z W T V : Type*} [Nonempty V]
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (n : ℕ)
    (h : ∃ side : X → Fin n, ∃ d,
      StochasticGraph.Decodes (jointChannel (sequential I J)).prob P side d) :
    ∃ side : X → Fin n, ∃ d, StochasticGraph.Decodes (jointChannel I).prob P side d := by
  obtain ⟨side, hd⟩ := h
  exact ⟨side, side_decoder_before_of_after I J P side hd⟩

/-- Recoverable continuations reflect every target conflict as well as preserving it.
The graph equality compares the same initial states, not merely the same graph cardinality. -/
theorem recoverable_continuation_graph_eq {X Y Z W T V : Type*}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (hJ : ∀ y, StochasticRecoverable (J y)) :
    StochasticGraph.conflictGraph (jointChannel (sequential I J)).prob P =
      StochasticGraph.conflictGraph (jointChannel I).prob P := by
  ext x x'
  constructor
  · rintro ⟨hP, ⟨⟨y, w⟩, t⟩, hx, hx'⟩
    obtain ⟨z, hi, hj⟩ := (sequential_positive_iff I J x y w t).mp hx
    obtain ⟨z', hi', hj'⟩ := (sequential_positive_iff I J x' y w t).mp hx'
    obtain ⟨restore, hr⟩ := hJ y
    have he : z = z' := (hr z w t hj).symm.trans (hr z' w t hj')
    subst z'
    exact ⟨hP, (y, z), hi, hi'⟩
  · exact sequential_conflict_persists I J P

/-- With recoverable continuations, an arbitrary side record solves exactly the same target
problem before and after the entire adaptive operation. -/
theorem recoverable_continuation_decoder_iff {X Y Z W T V C : Type*} [Nonempty V]
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (side : X → C) (hJ : ∀ y, StochasticRecoverable (J y)) :
    (∃ d, StochasticGraph.Decodes (jointChannel (sequential I J)).prob P side d) ↔
      ∃ d, StochasticGraph.Decodes (jointChannel I).prob P side d := by
  rw [StochasticGraph.decoder_iff_coloring, StochasticGraph.decoder_iff_coloring,
    recoverable_continuation_graph_eq I J P hJ]

/-- The exact chromatic side-information cost is unchanged by recoverable continuation. -/
theorem recoverable_continuation_chromatic_eq {X Y Z W T V : Type*}
    [Fintype Y] [Fintype Z] [Fintype W] [Fintype T]
    (I : StochasticInstrument X Y Z) (J : Y → StochasticInstrument Z W T)
    (P : X → V) (hJ : ∀ y, StochasticRecoverable (J y)) :
    (StochasticGraph.conflictGraph (jointChannel (sequential I J)).prob P).chromaticNumber =
      (StochasticGraph.conflictGraph (jointChannel I).prob P).chromaticNumber := by
  rw [recoverable_continuation_graph_eq I J P hJ]

/-- Keeping the bit and then erasing it preserves the first, silent outcome but strictly adds
a conflict between the two initial inputs. The recovery premise above cannot be dropped. -/
theorem erasure_strictly_adds_conflict :
    ¬ (StochasticGraph.conflictGraph (jointChannel (deterministic silentKeep)).prob id).Adj
        false true ∧
      (StochasticGraph.conflictGraph
        (jointChannel (sequential (deterministic silentKeep)
          (fun _ => deterministic silentErase))).prob id).Adj false true := by
  classical
  constructor
  · rintro ⟨_, ⟨y, z⟩, h0, h1⟩
    have hn : ¬ (false = z ∧ true = z) := by
      rintro ⟨he0, he1⟩
      have hbad : false = true := he0.trans he1.symm
      cases hbad
    by_cases hz : false = z
    · have hz' : ¬ true = z := fun he => hn ⟨hz, he⟩
      simp [jointChannel, deterministic, silentKeep, hz'] at h1
    · simp [jointChannel, deterministic, silentKeep, hz] at h0
  · refine ⟨by decide, (((), ()), false), ?_, ?_⟩
    · exact (sequential_positive_iff (deterministic silentKeep)
        (fun _ => deterministic silentErase) false () () false).mpr
        ⟨false, by simp [deterministic, silentKeep], by simp [deterministic, silentErase]⟩
    · exact (sequential_positive_iff (deterministic silentKeep)
        (fun _ => deterministic silentErase) true () () false).mpr
        ⟨true, by simp [deterministic, silentKeep], by simp [deterministic, silentErase]⟩

end OperatorKO7.Meta.BoundaryObserver.InstrumentComposition
