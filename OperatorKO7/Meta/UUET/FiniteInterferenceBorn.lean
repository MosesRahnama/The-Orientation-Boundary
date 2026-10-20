import OperatorKO7.Meta.UUET.FiniteComplexAmplitudeBorn

set_option autoImplicit false

/-!
# UUET finite interference / phase-sensitive Born ledger (U-64)

This uses the finite complex amplitude carrier (U-62) to mechanize *interference*:
amplitudes are added *before* the norm-square is taken, so the squared modulus of a
sum carries a cross term that the incoherent sum of intensities does not. A finite
two-path interference carrier records, via a `committed` flag, whether the boundary
event has formed a terminal record: an uncommitted carrier carries the live
interference term, a committed one collapses to the classical (incoherent) sum.

What is proven:
* `CAmp.normSq_add`: `normSq (A + B) = normSq A + normSq B + 2 * dot A B`;
* `interferenceTerm_eq`: the coherent-minus-incoherent deficit is exactly `2 * dot A B`;
* constructive `(1,0)+(1,0)` (intensity 4 vs sum 2, cross +2), destructive
 `(1,0)+(-1,0)` (intensity 0 vs sum 2, cross -2), and phase-orthogonal
 `(1,0)+(0,1)` (no cross term, intensity 2);
* `coherent_minus_incoherent`: the carrier's coherent and incoherent intensities
 differ by exactly the live interference term;
* `committed_no_interference` / `uncommitted_carries_interference`: the `committed`
 flag (the terminal-record license) controls whether interference is live;
* `interference_dual_boundary`: an uncommitted carrier carries the interference term
 while a committed terminal record (U-27) returns the normalized classical
 two-branch Born ledger and zero entanglement magnitude.

Scope and honesty: FINITE STRUCTURAL Lean over real pairs `(re, im)`. This is the
finite `|A + B|^2` interference algebra; it is NOT Hilbert-space quantum mechanics
(no complex Hilbert space, no state vector, no Born postulate). The reading as a
physical interference pattern is a structural model, not a Lean claim. No `sorry`,
`admit`, new `axiom`, `native_decide`, `bv_decide`, `@[csimp]`, `unsafe`, `partial`,
or `opaque`. Headline declarations are `#print axioms`-checked against the baseline
whitelist `{propext, Classical.choice, Quot.sound}`.
-/

namespace OperatorKO7.Meta.UUET

noncomputable section

namespace CAmp

/-- Finite complex amplitude addition (componentwise on the real pair). -/
def add (z w : CAmp) : CAmp := CAmp.mk (z.re + w.re) (z.im + w.im)

/-- Finite complex amplitude negation. -/
def neg (z : CAmp) : CAmp := CAmp.mk (-z.re) (-z.im)

/-- The real-pair dot product `re_z * re_w + im_z * im_w`. -/
def dot (z w : CAmp) : ℝ := z.re * w.re + z.im * w.im

/-- **Cross-term expansion.** The squared modulus of a sum is the sum of the
squared moduli plus twice the dot product (the interference cross term). -/
theorem normSq_add (z w : CAmp) :
    (z.add w).normSq = z.normSq + w.normSq + 2 * z.dot w := by
  simp only [add, normSq, dot]; ring

/-- `add` with the negation is the destructive combination. -/
theorem add_neg_self (z : CAmp) : (z.add z.neg).normSq = 0 := by
  simp only [add, neg, normSq]; ring

end CAmp

/-- The interference term: coherent intensity minus incoherent sum. -/
def interferenceTerm (z w : CAmp) : ℝ :=
  (z.add w).normSq - (z.normSq + w.normSq)

/-- **Interference deficit theorem.** The interference term equals exactly twice
the dot product (the cross term). -/
theorem interferenceTerm_eq (z w : CAmp) :
    interferenceTerm z w = 2 * z.dot w := by
  unfold interferenceTerm
  rw [CAmp.normSq_add]; ring

/-- **Constructive interference.** `(1,0)+(1,0)` has intensity 4 while the
incoherent sum is 2; the cross term is `+2`. -/
theorem constructive_interference :
    (CAmp.add (CAmp.mk 1 0) (CAmp.mk 1 0)).normSq = 4
      ∧ (CAmp.mk 1 0).normSq + (CAmp.mk 1 0).normSq = 2
      ∧ interferenceTerm (CAmp.mk 1 0) (CAmp.mk 1 0) = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [CAmp.add, CAmp.normSq, interferenceTerm] <;> norm_num

/-- **Destructive interference.** `(1,0)+(-1,0)` has intensity 0 while the
incoherent sum is 2; the cross term is `-2`. -/
theorem destructive_interference :
    (CAmp.add (CAmp.mk 1 0) (CAmp.mk (-1) 0)).normSq = 0
      ∧ (CAmp.mk 1 0).normSq + (CAmp.mk (-1) 0).normSq = 2
      ∧ interferenceTerm (CAmp.mk 1 0) (CAmp.mk (-1) 0) = -2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [CAmp.add, CAmp.normSq, interferenceTerm] <;> norm_num

/-- **Phase-orthogonal: no interference.** `(1,0)+(0,1)` has zero cross term and
intensity 2 (the incoherent sum). -/
theorem orthogonal_no_interference :
    interferenceTerm (CAmp.mk 1 0) (CAmp.mk 0 1) = 0
      ∧ (CAmp.add (CAmp.mk 1 0) (CAmp.mk 0 1)).normSq = 2
      ∧ (CAmp.mk 1 0).normSq + (CAmp.mk 0 1).normSq = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [CAmp.add, CAmp.normSq, interferenceTerm] <;> norm_num

/-- A finite two-path interference carrier: two branch amplitudes and a flag
recording whether the boundary event has committed a terminal record. -/
structure InterferenceCarrier where
  pathA : CAmp
  pathB : CAmp
  committed : Bool

namespace InterferenceCarrier

/-- Coherent (pre-record) intensity: the norm-square of the summed amplitude. -/
def coherentIntensity (c : InterferenceCarrier) : ℝ := (c.pathA.add c.pathB).normSq

/-- Incoherent (post-record) intensity: the sum of branch intensities. -/
def incoherentIntensity (c : InterferenceCarrier) : ℝ := c.pathA.normSq + c.pathB.normSq

/-- The live interference term carried by the two paths. -/
def liveInterference (c : InterferenceCarrier) : ℝ := interferenceTerm c.pathA c.pathB

/-- The observed intensity: incoherent (classical, no cross term) once committed,
coherent (interference live) while uncommitted. -/
def observedIntensity (c : InterferenceCarrier) : ℝ :=
  if c.committed then c.incoherentIntensity else c.coherentIntensity

end InterferenceCarrier

/-- **Coherent vs incoherent.** The carrier's coherent and incoherent intensities
differ by exactly the live interference term. -/
theorem coherent_minus_incoherent (c : InterferenceCarrier) :
    c.coherentIntensity - c.incoherentIntensity = c.liveInterference := by
  simp only [InterferenceCarrier.coherentIntensity, InterferenceCarrier.incoherentIntensity,
    InterferenceCarrier.liveInterference, interferenceTerm]

/-- **Committed: interference collapsed.** Once the terminal record commits, the
observed intensity is the classical incoherent sum (no cross term). -/
theorem committed_no_interference (c : InterferenceCarrier) (h : c.committed = true) :
    c.observedIntensity = c.incoherentIntensity := by
  simp only [InterferenceCarrier.observedIntensity, h, if_true]

/-- **Uncommitted: interference live.** While uncommitted, the observed intensity
carries the full interference term over the incoherent sum. -/
theorem uncommitted_carries_interference (c : InterferenceCarrier) (h : c.committed = false) :
    c.observedIntensity = c.incoherentIntensity + c.liveInterference := by
  have hco : c.observedIntensity = c.coherentIntensity := by
    simp [InterferenceCarrier.observedIntensity, h]
  rw [hco]
  linear_combination coherent_minus_incoherent c

/-- **Dual-boundary interference theorem.** Branch licensing controls interference:
an (uncommitted) carrier's coherent intensity is the incoherent sum plus the live
interference term, while a committed terminal record (U-27) returns the normalized
classical two-branch Born ledger and zero entanglement magnitude (interference
collapsed to a separable classical record). -/
theorem interference_dual_boundary
    (s : OperationalCompletenessState) (h : terminalRecordLicensed s)
    (p : ComplexBranchPair) (c : InterferenceCarrier) :
    c.coherentIntensity = c.incoherentIntensity + c.liveInterference
      ∧ cWeightA p + cWeightB p = 1
      ∧ 0 ≤ cWeightA p
      ∧ entanglementMagnitude (descentLicensedOf s) (distinctionLicensedOf s) = 0 := by
  refine ⟨?_, cWeights_normalized p, cWeightA_nonneg p,
    entanglementMagnitude_collapses_on_terminal_record s h⟩
  linear_combination coherent_minus_incoherent c

/-- A constructive interference carrier `(1,0)+(1,0)`, uncommitted. -/
def constructiveCarrier : InterferenceCarrier where
  pathA := CAmp.mk 1 0
  pathB := CAmp.mk 1 0
  committed := false

/-- A committed interference carrier (the same paths, terminal record formed). -/
def committedCarrier : InterferenceCarrier where
  pathA := CAmp.mk 1 0
  pathB := CAmp.mk 1 0
  committed := true

/-- Non-vacuity: constructive `+2`, destructive `-2`, orthogonal `0` cross terms;
the uncommitted carrier carries interference (observed `4`) while the committed one
collapses to the incoherent sum (`2`). -/
theorem finiteInterferenceBorn_nonvacuous :
    interferenceTerm (CAmp.mk 1 0) (CAmp.mk 1 0) = 2
      ∧ interferenceTerm (CAmp.mk 1 0) (CAmp.mk (-1) 0) = -2
      ∧ interferenceTerm (CAmp.mk 1 0) (CAmp.mk 0 1) = 0
      ∧ constructiveCarrier.observedIntensity = 4
      ∧ committedCarrier.observedIntensity = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [interferenceTerm, InterferenceCarrier.observedIntensity,
      InterferenceCarrier.coherentIntensity, InterferenceCarrier.incoherentIntensity,
      constructiveCarrier, committedCarrier, CAmp.add, CAmp.normSq] <;> norm_num

/-! ## U-67: finite real-pair phase interference model

A unit phase `(c, s)` with `c^2 + s^2 = 1` interferes with the reference amplitude
`(1, 0)`. The coherent intensity is `2 + 2c`: maximal (`4`) at `c = 1`, null (`0`) at
`c = -1`, and the incoherent value (`2`) at `c = 0`. A four-case scenario registry
records constructive, destructive, orthogonal, and committed-collapse outcomes. This
is still finite real-pair algebra, not Hilbert-space QM. -/

/-- A finite unit phase `(c, s)` with `c^2 + s^2 = 1`. -/
structure UnitPhase where
  c : ℝ
  s : ℝ
  unit : c ^ 2 + s ^ 2 = 1

/-- **Phase interference intensity.** Two unit amplitudes `(1, 0)` and `(c, s)` with
`c^2 + s^2 = 1` give coherent intensity `2 + 2c`. -/
theorem phase_coherent_intensity (p : UnitPhase) :
    (CAmp.add (CAmp.mk 1 0) (CAmp.mk p.c p.s)).normSq = 2 + 2 * p.c := by
  simp only [CAmp.add, CAmp.normSq]
  linear_combination p.unit

/-- Constructive phase `c = 1`. -/
def constructivePhase : UnitPhase := ⟨1, 0, by norm_num⟩

/-- Destructive phase `c = -1`. -/
def destructivePhase : UnitPhase := ⟨-1, 0, by norm_num⟩

/-- Orthogonal phase `c = 0`, `s = 1`. -/
def orthogonalPhase : UnitPhase := ⟨0, 1, by norm_num⟩

/-- A finite two-path interference scenario. -/
inductive PhaseScenario where
  | constructive
  | destructive
  | orthogonal
  | committedCollapse
  deriving DecidableEq, Repr

/-- The observed intensity of each scenario (`committedCollapse` is the classical sum). -/
def PhaseScenario.intensity : PhaseScenario → ℝ
  | .constructive => 4
  | .destructive => 0
  | .orthogonal => 2
  | .committedCollapse => 2

/-- The finite registry of interference scenarios. -/
def phaseScenarioRegistry : List PhaseScenario :=
  [.constructive, .destructive, .orthogonal, .committedCollapse]

theorem phaseScenarioRegistry_length : phaseScenarioRegistry.length = 4 := rfl

/-- **Scenario intensities match the phase model.** Each registry intensity equals the
coherent intensity of its phase; committed-collapse equals the committed carrier's
observed intensity. -/
theorem phaseScenario_intensity_matches :
    PhaseScenario.constructive.intensity
        = (CAmp.add (CAmp.mk 1 0) (CAmp.mk constructivePhase.c constructivePhase.s)).normSq
      ∧ PhaseScenario.destructive.intensity
        = (CAmp.add (CAmp.mk 1 0) (CAmp.mk destructivePhase.c destructivePhase.s)).normSq
      ∧ PhaseScenario.orthogonal.intensity
        = (CAmp.add (CAmp.mk 1 0) (CAmp.mk orthogonalPhase.c orthogonalPhase.s)).normSq
      ∧ PhaseScenario.committedCollapse.intensity = committedCarrier.observedIntensity := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [phase_coherent_intensity constructivePhase]
    norm_num [PhaseScenario.intensity, constructivePhase]
  · rw [phase_coherent_intensity destructivePhase]
    norm_num [PhaseScenario.intensity, destructivePhase]
  · rw [phase_coherent_intensity orthogonalPhase]
    norm_num [PhaseScenario.intensity, orthogonalPhase]
  · have h2 : committedCarrier.observedIntensity = 2 := finiteInterferenceBorn_nonvacuous.2.2.2.2
    simp only [PhaseScenario.intensity, h2]

/-- **Phase dual-boundary theorem.** For a unit phase `p`, the uncommitted carrier
shows phase interference intensity `2 + 2c`, while a committed terminal record (U-27)
collapses to the classical sum `2` and carries zero entanglement magnitude. -/
theorem phase_interference_dual_boundary
    (st : OperationalCompletenessState) (h : terminalRecordLicensed st) (p : UnitPhase) :
    (CAmp.add (CAmp.mk 1 0) (CAmp.mk p.c p.s)).normSq = 2 + 2 * p.c
      ∧ committedCarrier.observedIntensity = 2
      ∧ entanglementMagnitude (descentLicensedOf st) (distinctionLicensedOf st) = 0 :=
  ⟨phase_coherent_intensity p, finiteInterferenceBorn_nonvacuous.2.2.2.2,
    entanglementMagnitude_collapses_on_terminal_record st h⟩

/-- Non-vacuity of the phase model: constructive `4`, destructive `0`, orthogonal `2`,
registry length `4`. -/
theorem finitePhaseInterference_nonvacuous :
    (CAmp.add (CAmp.mk 1 0) (CAmp.mk constructivePhase.c constructivePhase.s)).normSq = 4
      ∧ (CAmp.add (CAmp.mk 1 0) (CAmp.mk destructivePhase.c destructivePhase.s)).normSq = 0
      ∧ (CAmp.add (CAmp.mk 1 0) (CAmp.mk orthogonalPhase.c orthogonalPhase.s)).normSq = 2
      ∧ phaseScenarioRegistry.length = 4 := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [phase_coherent_intensity constructivePhase]; norm_num [constructivePhase]
  · rw [phase_coherent_intensity destructivePhase]; norm_num [destructivePhase]
  · rw [phase_coherent_intensity orthogonalPhase]; norm_num [orthogonalPhase]

#print axioms phase_coherent_intensity
#print axioms phaseScenarioRegistry_length
#print axioms phaseScenario_intensity_matches
#print axioms phase_interference_dual_boundary
#print axioms finitePhaseInterference_nonvacuous

#print axioms CAmp.normSq_add
#print axioms interferenceTerm_eq
#print axioms constructive_interference
#print axioms destructive_interference
#print axioms orthogonal_no_interference
#print axioms coherent_minus_incoherent
#print axioms committed_no_interference
#print axioms uncommitted_carries_interference
#print axioms interference_dual_boundary
#print axioms finiteInterferenceBorn_nonvacuous

end

end OperatorKO7.Meta.UUET
