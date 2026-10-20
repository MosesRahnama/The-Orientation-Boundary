import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

/-!
# Finite observer realization

Theorem 11.2(ii) of the Observation Principle manuscript.
The construction glues two binary rows over one shared binary report.
Relation: none. Trust: kernel-only.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ObserverRealization

open FourTestTables

/-- A law on any finite record type is a law on an indexed finite type. -/
theorem hasObserver_of_fintype {L : Type*} [Fintype L] {d : Table}
    (w : L → ℝ) (A B : Bool → L → Bool) (hw : ∀ l, 0 ≤ w l)
    (hs : ∑ l, w l = 1)
    (hd : ∀ x y, d x y = ∑ l, if A x l ≠ B y l then w l else 0) : HasObserver d := by
  classical
  let e := Fintype.equivFin L
  refine ⟨Fintype.card L, fun l => w (e.symm l),
    fun x l => A x (e.symm l), fun y l => B y (e.symm l),
    fun l => hw (e.symm l), ?_, ?_⟩
  · exact (e.symm.sum_comp w).trans hs
  · intro x y
    exact (hd x y).trans
      (e.symm.sum_comp (fun l => if A x l ≠ B y l then w l else 0)).symm

/-- Gluing two nonnegative rows of the same mass preserves the first marginal,
including a row of zero mass. -/
theorem sum_glue_left {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (m : ℝ)
    (hp : ∀ a, 0 ≤ p a) (hps : ∑ a, p a = m) (hqs : ∑ b, q b = m) (a : A) :
    (∑ b, p a * q b / m) = p a := by
  by_cases hm : m = 0
  · have ha : p a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hp i)).mp (hps.trans hm) a
        (Finset.mem_univ _)
    simp [ha]
  · rw [← Finset.sum_div, ← Finset.mul_sum, hqs]
    exact mul_div_cancel_right₀ (p a) hm

/-- The other marginal of the same glued law. -/
theorem sum_glue_right {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (m : ℝ)
    (hq : ∀ b, 0 ≤ q b) (hps : ∑ a, p a = m) (hqs : ∑ b, q b = m) (b : B) :
    (∑ a, p a * q b / m) = q b := by
  simp_rw [mul_comm (p _) (q b)]
  exact sum_glue_left q p m hq hqs hps b

/-- Joint weights of an answer and the second report when the first report is false.
The rates of disagreement with the two reports are `a` and `b`. -/
noncomputable def binaryRow (a b t : ℝ) (c p : Bool) : ℝ :=
  if c then (if p then (a - b + t) / 2 else (-a + b + t) / 2)
  else (if p then (a + b - t) / 2 else (2 - a - b - t) / 2)

/-- The mass of the common report. -/
noncomputable def binaryMass (t : ℝ) (c : Bool) : ℝ := if c then t else 1 - t

/-- The interval conditions are precisely what makes every cell nonnegative. -/
theorem binaryRow_nonneg {a b t : ℝ} (hl : |a - b| ≤ t) (hu : t ≤ a + b)
    (hs : a + b + t ≤ 2) (c p : Bool) : 0 ≤ binaryRow a b t c p := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hl
  cases c <;> cases p <;> simp only [binaryRow, Bool.false_eq_true, if_false, if_true] <;> linarith

/-- Each row has the prescribed common-report mass. -/
theorem binaryRow_sum (a b t : ℝ) (c : Bool) :
    (∑ p, binaryRow a b t c p) = binaryMass t c := by
  rw [Fintype.sum_bool]
  cases c <;> simp only [binaryRow, binaryMass, Bool.false_eq_true, if_false, if_true] <;> ring

/-- The cycle conditions supply one common disagreement rate for the two rows. -/
theorem cycle_common_rate (d : Table) (hd : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1)
    (hc : CycleIneq d 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      (∀ x, |d x false - d x true| ≤ t ∧ t ≤ d x false + d x true ∧
        d x false + d x true + t ≤ 2) := by
  obtain ⟨a00, b00⟩ := hc false false
  obtain ⟨a01, b01⟩ := hc false true
  obtain ⟨a10, b10⟩ := hc true false
  obtain ⟨a11, b11⟩ := hc true true
  have h00 := hd false false
  have h01 := hd false true
  have h10 := hd true false
  have h11 := hd true true
  let t := max |d false false - d false true| |d true false - d true true|
  have hl0 : |d false false - d false true| ≤ t := le_max_left _ _
  have hl1 : |d true false - d true true| ≤ t := le_max_right _ _
  refine ⟨t, (abs_nonneg _).trans hl0, ?_, ?_⟩
  · exact max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
  · intro x
    have hu0 : t ≤ d false false + d false true :=
      max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hu1 : t ≤ d true false + d true true :=
      max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hs0 : t ≤ 2 - d false false - d false true :=
      max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hs1 : t ≤ 2 - d true false - d true true :=
      max_le (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)
    cases x
    · exact ⟨hl0, hu0, by linarith⟩
    · exact ⟨hl1, hu1, by linarith⟩

/--
The missing Fine converse for the manuscript's four correlation rates.
Constructs eight shared records by gluing two nonnegative binary laws.
No joint-observer or Fine theorem is assumed.
-/
theorem observer_of_cycle (d : Table) (hd : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1)
    (hc : CycleIneq d 1) : HasObserver d := by
  obtain ⟨t, ht0, ht1, hr⟩ := cycle_common_rate d hd hc
  let p := binaryRow (d false false) (d false true) t
  let q := binaryRow (d true false) (d true true) t
  let m := binaryMass t
  have hp : ∀ c a, 0 ≤ p c a := binaryRow_nonneg (hr false).1 (hr false).2.1 (hr false).2.2
  have hq : ∀ c b, 0 ≤ q c b := binaryRow_nonneg (hr true).1 (hr true).2.1 (hr true).2.2
  have hm : ∀ c, 0 ≤ m c := by
    intro c
    cases c <;> dsimp [m, binaryMass] <;> linarith
  have hps : ∀ c, (∑ a, p c a) = m c := binaryRow_sum _ _ _
  have hqs : ∀ c, (∑ b, q c b) = m c := binaryRow_sum _ _ _
  let w : Bool → Bool → Bool → ℝ := fun c a b => p c a * q c b / m c
  have hw : ∀ c a b, 0 ≤ w c a b :=
    fun c a b => div_nonneg (mul_nonneg (hp c a) (hq c b)) (hm c)
  have hleft : ∀ c a, (∑ b, w c a b) = p c a :=
    fun c a => sum_glue_left (p c) (q c) (m c) (hp c) (hps c) (hqs c) a
  have hright : ∀ c b, (∑ a, w c a b) = q c b :=
    fun c b => sum_glue_right (p c) (q c) (m c) (hq c) (hps c) (hqs c) b
  apply hasObserver_of_fintype (fun z : Bool × Bool × Bool => w z.1 z.2.1 z.2.2)
    (fun x z => if x then z.2.2 else z.2.1) (fun y z => if y then z.1 else false)
    (fun z => hw _ _ _)
  · simp only [Fintype.sum_prod_type]
    simp_rw [hleft, hps]
    rw [Fintype.sum_bool]
    dsimp [m, binaryMass]
    ring
  · have hlt := hleft true true
    have hlf := hleft false true
    have hlt' := hleft true false
    have hlf' := hleft false false
    have hrt := hright true true
    have hrf := hright false true
    have hrt' := hright true false
    have hrf' := hright false false
    simp only [Fintype.sum_bool] at hlt hlf hlt' hlf' hrt hrf hrt' hrf'
    dsimp [p, q, binaryRow] at hlt hlf hlt' hlf' hrt hrf hrt' hrf'
    intro x y
    cases x <;> cases y <;>
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false,
        ne_eq, not_true_eq_false, not_false_eq_true, if_false, if_true, add_zero, zero_add] <;>
      linarith

/-- The full rate-table characterization, including both directions. -/
theorem hasObserver_iff_cycle (d : Table) (hd : ∀ x y, 0 ≤ d x y ∧ d x y ≤ 1) :
    HasObserver d ↔ CycleIneq d 1 :=
  ⟨observer_cycleIneq, observer_of_cycle d hd⟩

/-! ## A common law for an arbitrary finite family of reports -/

/-- The reported vector is the average of deterministic report vectors under a probability law
on the allowed complete assignments. The assignment type may be empty. -/
def Realizable {A J : Type*} [Fintype A] (v : A → J → ℝ) (p : J → ℝ) : Prop :=
  ∃ w : A → ℝ, (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧ (∑ a, w a • v a = p)

/-- A common law is exactly a point of the convex hull of the complete assignments.
This constructs weights on the stated assignment type, not on an assumed hidden carrier. -/
theorem realizable_iff_mem_convexHull {A J : Type*} [Fintype A]
    (v : A → J → ℝ) (p : J → ℝ) :
    Realizable v p ↔ p ∈ convexHull ℝ (Set.range v) := by
  classical
  constructor
  · rintro ⟨w, hw, hs, he⟩
    exact mem_convexHull_of_exists_fintype w v hw hs (fun a => ⟨a, rfl⟩) he
  · intro h
    obtain ⟨I, _, w, z, hw, hs, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp h
    choose g hg using hz
    refine ⟨fun a => ∑ i, if g i = a then w i else 0, ?_, ?_, ?_⟩
    · intro a
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact hw i | exact le_rfl
    · rw [Finset.sum_comm]
      simpa using hs
    · calc
        (∑ a, (∑ i, if g i = a then w i else 0) • v a)
            = ∑ a, ∑ i, if g i = a then w i • v a else 0 := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.sum_smul]
                apply Finset.sum_congr rfl
                intro i _
                split_ifs <;> simp
        _ = ∑ i, ∑ a, if g i = a then w i • v a else 0 := Finset.sum_comm
        _ = ∑ i, w i • z i := by simp [hg]
        _ = p := he

/-- A linear score of a finite report vector. -/
noncomputable def reportScore {J : Type*} [Fintype J] (c p : J → ℝ) : ℝ :=
  ∑ j, c j * p j

/-- Every linear functional on a finite report space is a score of its coordinates. -/
theorem functional_eq_reportScore {J : Type*} [Fintype J] [DecidableEq J]
    (f : (J → ℝ) →L[ℝ] ℝ) (p : J → ℝ) :
    f p = reportScore (fun j => f (fun k => if j = k then 1 else 0)) p := by
  classical
  calc
    f p = ∑ j, p j • f (fun k => if j = k then 1 else 0) :=
      LinearMap.pi_apply_eq_sum_univ f.toLinearMap p
    _ = reportScore (fun j => f (fun k => if j = k then 1 else 0)) p := by
      simp only [reportScore, smul_eq_mul, mul_comm]

/-- Every bound valid on the complete assignments holds for every common-law report. -/
theorem score_le_of_realizable {A J : Type*} [Fintype A] [Fintype J]
    {v : A → J → ℝ} {p : J → ℝ} (h : Realizable v p)
    (c : J → ℝ) (b : ℝ) (hb : ∀ a, reportScore c (v a) ≤ b) :
    reportScore c p ≤ b := by
  obtain ⟨w, hw, hs, rfl⟩ := h
  have he : reportScore c (∑ a, w a • v a) = ∑ a, w a * reportScore c (v a) := by
    simp only [reportScore, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    (∑ a, w a * reportScore c (v a)) ≤ ∑ a, w a * b :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hb a) (hw a)
    _ = b := by rw [← Finset.sum_mul, hs, one_mul]

/-- A family without a common law has a finite linear inequality that every allowed complete
assignment obeys and that the family violates. No separating inequality is assumed. -/
theorem not_realizable_iff_separating_score {A J : Type*} [Fintype A] [Fintype J]
    (v : A → J → ℝ) (p : J → ℝ) :
    ¬ Realizable v p ↔
      ∃ (c : J → ℝ) (b : ℝ), (∀ a, reportScore c (v a) ≤ b) ∧ b < reportScore c p := by
  classical
  constructor
  · intro h
    have hnot : p ∉ convexHull ℝ (Set.range v) :=
      fun hp => h ((realizable_iff_mem_convexHull v p).mpr hp)
    obtain ⟨f, b, hf, hp⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull (Set.finite_range v)) hnot
    refine ⟨fun j => f (fun k => if j = k then 1 else 0), b, ?_, ?_⟩
    · intro a
      rw [← functional_eq_reportScore]
      exact (hf _ (subset_convexHull ℝ _ ⟨a, rfl⟩)).le
    · rwa [functional_eq_reportScore] at hp
  · rintro ⟨c, b, hv, hp⟩ h
    exact (not_lt_of_ge (score_le_of_realizable h c b hv)) hp

/-- Existence and obstruction are exhaustive and mutually exclusive at any finite set of
allowed complete assignments. -/
theorem common_law_or_certificate {A J : Type*} [Fintype A] [Fintype J]
    (v : A → J → ℝ) (p : J → ℝ) :
    Realizable v p ∨
      ∃ (c : J → ℝ) (b : ℝ), (∀ a, reportScore c (v a) ≤ b) ∧ b < reportScore c p := by
  classical
  by_cases h : Realizable v p
  · exact Or.inl h
  · exact Or.inr ((not_realizable_iff_separating_score v p).mp h)

/-- The violation of a valid inequality is bounded by the weighted change in the reports.
Thus the inequality certifies a quantitative cost of every repair, not only failure of exact
realization. -/
theorem separating_score_repair_bound {A J : Type*} [Fintype A] [Fintype J]
    {v : A → J → ℝ} {p r : J → ℝ} (hr : Realizable v r)
    (c : J → ℝ) (b : ℝ) (hb : ∀ a, reportScore c (v a) ≤ b) :
    reportScore c p - b ≤ ∑ j, |c j| * |p j - r j| := by
  have hscore := score_le_of_realizable hr c b hb
  have he : reportScore c p - reportScore c r = ∑ j, c j * (p j - r j) := by
    simp only [reportScore, Finset.sum_sub_distrib, mul_sub]
  calc
    reportScore c p - b ≤ reportScore c p - reportScore c r := by linarith
    _ = ∑ j, c j * (p j - r j) := he
    _ ≤ ∑ j, |c j| * |p j - r j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [← abs_mul]
      exact le_abs_self _

/-- A measurement context reports the restriction of a complete assignment. This vector
contains the probability of every outcome at every context, including overlapping contexts. -/
noncomputable def contextVector {I O C : Type*} (context : C → Finset I)
    (a : I → O) : (Σ c, ({i // i ∈ context c} → O)) → ℝ := by
  classical
  exact fun j => if (fun i : {i // i ∈ context j.1} => a i.1) = j.2 then 1 else 0

attribute [local instance] Classical.propDecidable

/-- A common probability law on all complete assignments reproduces every supplied context
probability precisely when the corresponding vector is realizable. -/
theorem context_realizable_iff {I O C : Type*} [Fintype I] [Fintype O]
    (context : C → Finset I) (p : (Σ c, ({i // i ∈ context c} → O)) → ℝ) :
    Realizable (contextVector context) p ↔
      ∃ w : (I → O) → ℝ, (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
        ∀ c (s : {i // i ∈ context c} → O),
          p ⟨c, s⟩ = ∑ a, if (fun i : {i // i ∈ context c} => a i.1) = s then w a else 0 := by
  classical
  constructor
  · rintro ⟨w, hw, hs, he⟩
    refine ⟨w, hw, hs, ?_⟩
    intro c s
    have h := congrFun he ⟨c, s⟩
    simpa [contextVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  · rintro ⟨w, hw, hs, hp⟩
    refine ⟨w, hw, hs, funext fun ⟨c, s⟩ => ?_⟩
    simpa [contextVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using (hp c s).symm

/-- Every family of finitely many finite measurement contexts admits either a common law on
complete assignments or an explicit linear obstruction on its reported probabilities. -/
theorem context_law_or_certificate {I O C : Type*} [Fintype I] [Fintype O] [Fintype C]
    (context : C → Finset I) (p : (Σ c, ({i // i ∈ context c} → O)) → ℝ) :
    Realizable (contextVector context) p ∨
      ∃ (c : (Σ k, ({i // i ∈ context k} → O)) → ℝ) (b : ℝ),
        (∀ a : I → O, reportScore c (contextVector context a) ≤ b) ∧ b < reportScore c p :=
  common_law_or_certificate (contextVector context) p

/-- Any finite hidden-record model induces a law on the allowed complete assignments. -/
theorem realizable_of_hidden {A J L : Type*} [Fintype A] [Fintype L]
    (v : A → J → ℝ) (p : J → ℝ) (assignment : L → A) (w : L → ℝ)
    (hw : ∀ l, 0 ≤ w l) (hs : ∑ l, w l = 1)
    (hp : ∑ l, w l • v (assignment l) = p) : Realizable v p :=
  (realizable_iff_mem_convexHull v p).mpr
    (mem_convexHull_of_exists_fintype w (v ∘ assignment) hw hs
      (fun l => ⟨assignment l, rfl⟩) hp)

/-- Duplicating hidden labels without changing the allowed deterministic reports changes no
realizability question. Thus adding hidden bits cannot repair a forbidden report vector by
itself. -/
theorem realizable_iff_reindex {A B J : Type*} [Fintype A] [Fintype B]
    (v : A → J → ℝ) (e : B → A) (he : Function.Surjective e) (p : J → ℝ) :
    Realizable (v ∘ e) p ↔ Realizable v p := by
  rw [realizable_iff_mem_convexHull, realizable_iff_mem_convexHull]
  have hr : Set.range (v ∘ e) = Set.range v := by
    ext z
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨e b, hb⟩
    · rintro ⟨a, ha⟩
      obtain ⟨b, rfl⟩ := he a
      exact ⟨b, ha⟩
  rw [hr]

/-- A deterministic report is realized by the unit mass at its assignment. -/
theorem realizable_vertex {A J : Type*} [Fintype A] (v : A → J → ℝ) (a : A) :
    Realizable v (v a) :=
  (realizable_iff_mem_convexHull v (v a)).mpr (subset_convexHull ℝ _ ⟨a, rfl⟩)

/-- Reports of differences around three overlapping binary tests. -/
def triangleReport (a : Bool × Bool × Bool) : Fin 3 → ℝ :=
  ![if a.1 ≠ a.2.1 then 1 else 0,
    if a.2.1 ≠ a.2.2 then 1 else 0,
    if a.2.2 ≠ a.1 then 1 else 0]

/-- Three binary values cannot all differ in a cycle. -/
theorem triangle_score_le (a : Bool × Bool × Bool) :
    reportScore (fun _ => 1) (triangleReport a) ≤ 2 := by
  rcases a with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    norm_num [reportScore, triangleReport, Fin.sum_univ_succ]

/-- Every individual edge can report certain difference, but the three reports have no common
law. This is a nonempty, finite incompatibility example. -/
theorem triangle_not_realizable : ¬ Realizable triangleReport (fun _ => 1) := by
  apply (not_realizable_iff_separating_score triangleReport (fun _ => 1)).mpr
  refine ⟨fun _ => 1, 2, triangle_score_le, ?_⟩
  norm_num [reportScore, Fin.sum_univ_succ]

/-- Every common-law repair of the inconsistent triangle changes its rates by at least one
in total absolute error. -/
theorem triangle_repair_lower {r : Fin 3 → ℝ} (hr : Realizable triangleReport r) :
    1 ≤ ∑ j, |1 - r j| := by
  have h := separating_score_repair_bound (p := fun _ => 1) hr
    (fun _ => 1) 2 triangle_score_le
  norm_num [reportScore, Fin.sum_univ_succ] at h ⊢
  exact h

/-- The bound of one is attained by averaging the three single-bit assignments. -/
theorem triangle_optimal_repair : Realizable triangleReport (fun _ => (2 : ℝ) / 3) ∧
    (∑ _j : Fin 3, |1 - (2 : ℝ) / 3|) = 1 := by
  constructor
  · apply realizable_of_hidden triangleReport (fun _ => (2 : ℝ) / 3)
      (![ (true, false, false), (false, true, false), (false, false, true)] :
        Fin 3 → Bool × Bool × Bool) (fun _ => (1 : ℝ) / 3)
    · intro l
      norm_num
    · norm_num [Fin.sum_univ_succ]
    · ext j
      fin_cases j <;>
        norm_num [Fin.sum_univ_succ, triangleReport, Pi.smul_apply, smul_eq_mul]
  · have ha : |1 - (2 : ℝ) / 3| = (1 : ℝ) / 3 := by
      rw [abs_of_nonneg (by norm_num)]
      norm_num
    simp_rw [ha]
    norm_num

end OperatorKO7.Meta.BoundaryObserver.ObserverRealization
