import OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional
import OperatorKO7.Meta.RepShift_BottleneckPredicate

/-!
# Witness depths for the free recursor

Direct witnesses are payload-sensitive expressions in the reflected two-coordinate
grammar, evaluated on actual terms. Every numeric successor profile is attained.
Imported witnesses are arbitrary natural rankings of the two root rules; their
pointwise least ranking is the executable root derivation height.

The second hierarchy additionally requires a counter-erasing signature decoder
at its imported level. Its impossibility is proved from two actual terms with
different transformed calls. Depth two instead contains the extracted-call
certificate. The depth equalities concern these declared languages, not every
possible language or every signature homomorphism.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.Recursor.RecursorFreeAlgebra
open OperatorKO7.Meta.Recursor.DPConfessionLicenseUnconditional
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.Rewriting
open OperatorKO7.RepShift

def counterObservation : RecursorTerm → Nat
  | .recR b _ n => deltaPrefix n + counterObservation b
  | .app _ t => counterObservation t
  | _ => 0

def payloadObservation : RecursorTerm → Nat
  | .recR b _ _ => payloadObservation b
  | .app a b => payloadObservation a + payloadObservation b + 1
  | _ => 0

def counterTerm : Nat → RecursorTerm
  | 0 => .void
  | n + 1 => .delta (counterTerm n)

def payloadTerm : Nat → RecursorTerm
  | 0 => .void
  | n + 1 => .app .void (payloadTerm n)

theorem deltaPrefix_counterTerm (n : Nat) : deltaPrefix (counterTerm n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [counterTerm, deltaPrefix, ih]

theorem counterObservation_payloadTerm (n : Nat) :
    counterObservation (payloadTerm n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem payloadObservation_payloadTerm (n : Nat) :
    payloadObservation (payloadTerm n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [payloadTerm, payloadObservation, ih]

def profileMeasure (m : Nat → Nat → Nat) (t : RecursorTerm) : Nat :=
  m (counterObservation t) (payloadObservation t)

theorem successor_profile (b s n : RecursorTerm) :
    counterObservation (.recR b s (.delta n)) =
        counterObservation (.app s (.recR b s n)) + 1 ∧
      payloadObservation (.app s (.recR b s n)) =
        payloadObservation (.recR b s (.delta n)) + (payloadObservation s + 1) := by
  simp only [counterObservation, payloadObservation, deltaPrefix]
  omega

/-- All counter, payload and positive growth values occur in actual root steps. -/
theorem every_successor_profile_attained (c p L : Nat) (hL : 1 ≤ L) :
    ∃ a b : RecursorTerm, FreeRecursorStep a b ∧
      counterObservation a = c + 1 ∧ payloadObservation a = p ∧
      counterObservation b = c ∧ payloadObservation b = p + L := by
  refine ⟨.recR (payloadTerm p) (payloadTerm (L - 1)) (.delta (counterTerm c)),
    .app (payloadTerm (L - 1)) (.recR (payloadTerm p) (payloadTerm (L - 1)) (counterTerm c)),
    .succ _ _ _, ?_, ?_, ?_, ?_⟩
  all_goals simp only [counterObservation, payloadObservation, deltaPrefix,
    deltaPrefix_counterTerm, counterObservation_payloadTerm, payloadObservation_payloadTerm]
  all_goals omega

theorem profile_orients_successors_iff (m : Nat → Nat → Nat) :
    (∀ b s n, profileMeasure m (.app s (.recR b s n)) <
      profileMeasure m (.recR b s (.delta n))) ↔ OrientsDupStep m := by
  constructor
  · intro h c p L hL
    have he := h (payloadTerm p) (payloadTerm (L - 1)) (counterTerm c)
    have hL' : L - 1 + p + 1 = p + L := by omega
    simpa only [profileMeasure, counterObservation, payloadObservation, deltaPrefix,
      deltaPrefix_counterTerm, counterObservation_payloadTerm,
      payloadObservation_payloadTerm, Nat.add_zero, hL'] using he
  · intro h b s n
    obtain ⟨hc, hp⟩ := successor_profile b s n
    unfold profileMeasure
    rw [hc, hp]
    exact h _ _ _ (Nat.succ_le_succ (Nat.zero_le _))

structure DirectWholeWitness where
  expression : MeasureExpr
  formation : DirectGrammarDerivation expression
  usesPayload : UsesPayload expression
  decreases : ∀ {a b}, FreeRecursorStep a b →
    profileMeasure expression.eval b < profileMeasure expression.eval a

theorem freeRecursor_no_directWhole : ¬ Nonempty DirectWholeWitness := by
  rintro ⟨w⟩
  exact no_directGrammar_measure_usesPayload_and_orients w.expression
    ⟨w.usesPayload, (profile_orients_successors_iff w.expression.eval).mp
      (fun b s n => w.decreases (.succ b s n))⟩

structure ImportedWholeWitness where
  ranking : RecursorTerm → Nat
  decreases : ∀ {a b}, FreeRecursorStep a b → ranking b < ranking a

theorem ImportedWholeWitness.wellFounded (w : ImportedWholeWitness) :
    WellFounded (fun a b => FreeRecursorStep b a) :=
  Subrelation.wf (fun h => w.decreases h) (measure w.ranking).wf

def derivationHeight : RecursorTerm → Nat := rootMachine.cost

theorem derivationHeight_step {a b : RecursorTerm} (h : FreeRecursorStep a b) :
    derivationHeight a = derivationHeight b + 1 :=
  rootMachine.cost_step (rootNext_iff.mpr h)

def importedWholeWitness : ImportedWholeWitness where
  ranking := derivationHeight
  decreases := fun h => by rw [derivationHeight_step h]; exact Nat.lt_succ_self _

theorem freeRecursor_has_importedWhole : Nonempty ImportedWholeWitness :=
  ⟨importedWholeWitness⟩

/-- Every natural root ranking bounds the actual length of every root path. -/
theorem ImportedWholeWitness.bounds_steps (w : ImportedWholeWitness)
    {n : Nat} {a b : RecursorTerm} (h : rootMachine.Steps n a b) :
    w.ranking b + n ≤ w.ranking a := by
  induction h with
  | refl => omega
  | cons hs _ ih =>
    have hd := w.decreases (rootNext_iff.mp hs)
    omega

theorem derivationHeight_pointwise_least (w : ImportedWholeWitness) (a : RecursorTerm) :
    derivationHeight a ≤ w.ranking a := by
  have h := w.bounds_steps (rootMachine.normalizing_steps a)
  change w.ranking (rootMachine.normalize a) + derivationHeight a ≤ w.ranking a at h
  omega

theorem derivationHeight_zero_rule (b s : RecursorTerm) :
    derivationHeight (.recR b s .void) = derivationHeight b + 1 :=
  derivationHeight_step (.zero b s)

theorem derivationHeight_successor (b s n : RecursorTerm) :
    derivationHeight (.recR b s (.delta n)) = 1 :=
  freeRecursor_successor_root_cost b s n

/-- The whole-term height cannot be reconstructed from the declared profile. -/
theorem derivationHeight_not_profile_factored :
    ¬ ∃ m : Nat → Nat → Nat, ∀ t, derivationHeight t = profileMeasure m t := by
  rintro ⟨m, hm⟩
  have h0 := hm .void
  have h1 := hm (.recR .void .void .void)
  have hz : derivationHeight .void = 0 := rootMachine.cost_terminal rfl
  rw [derivationHeight_zero_rule, hz] at h1
  rw [hz] at h0
  simp only [profileMeasure, counterObservation, payloadObservation, deltaPrefix] at h0 h1
  exact Nat.zero_ne_one (h0.trans h1.symm)

structure TransformedCallWitness where
  extractor : RecursorTerm → RecursorTerm → Option RecursorTerm
  extraction_exact : ∀ a rhs c, extractor a rhs = some c ↔
    FreeRecursorStep a rhs ∧ FreeRecursorDPPair a c
  ranking : RecursorTerm → Nat
  decreases : ∀ {a c}, FreeRecursorDPPair a c → ranking c < ranking a

def transformedCallWitness : TransformedCallWitness where
  extractor := extractCall
  extraction_exact := by
    intro a rhs c
    exact ⟨freeRecursor_extraction_sound,
      fun h => (freeRecursor_extraction_complete h.1).mpr h.2⟩
  ranking := dpRank
  decreases := freeRecursor_dp_rank_decreases

theorem TransformedCallWitness.wellFounded (w : TransformedCallWitness) :
    WellFounded (fun a b => FreeRecursorDPPair b a) :=
  Subrelation.wf (fun h => w.decreases h) (measure w.ranking).wf

theorem freeRecursor_has_transformedCall : Nonempty TransformedCallWitness :=
  ⟨transformedCallWitness⟩

/-- A signature observer that erases the counter cannot decide the actual call. -/
theorem erased_counter_cannot_decode_dp {α : Type} (S : SigmaAlgebra α)
    (observe : RecursorTerm → α) (hom : IsSigmaHomomorphism observe S)
    (erases : RecRConstantInThird S) :
    ¬ ∃ decode : α → Option RecursorTerm, ∀ t, decode (observe t) = dpNext t := by
  rintro ⟨decode, hd⟩
  have he := congrArg decode
    (dp_projection_not_in_recursor_signature_unconditional S observe hom erases)
  rw [hd, hd] at he
  change (none : Option RecursorTerm) = some (.recR .void .void .void) at he
  cases he

structure ErasedCounterDecoder where
  algebra : SigmaAlgebra Nat
  observe : RecursorTerm → Nat
  hom : IsSigmaHomomorphism observe algebra
  erases : RecRConstantInThird algebra
  decode : Nat → Option RecursorTerm
  correct : ∀ t, decode (observe t) = dpNext t

theorem no_erasedCounterDecoder : ¬ Nonempty ErasedCounterDecoder := by
  rintro ⟨w⟩
  exact erased_counter_cannot_decode_dp w.algebra w.observe w.hom w.erases
    ⟨w.decode, w.correct⟩

def RootTerminates (t : RecursorTerm) : Prop :=
  Acc (fun a b => FreeRecursorStep b a) t

def ExternalWitness : Type := PLift (WellFounded (fun a b => FreeRecursorStep b a))

def externalWitness : ExternalWitness := ⟨freeRecursor_step_rev_wellFounded⟩

def TruthEvidence : Nat → Type
  | 0 => DirectWholeWitness
  | 1 => ImportedWholeWitness
  | 2 => TransformedCallWitness
  | _ + 3 => ExternalWitness

/-- This declared language requires a counter-erasing signature decoder before
the transformed-call level, instead of admitting arbitrary state decoders. -/
def BoundaryEvidence : Nat → Type
  | 0 => DirectWholeWitness
  | 1 => ImportedWholeWitness × ErasedCounterDecoder
  | 2 => TransformedCallWitness
  | _ + 3 => ExternalWitness

theorem truthEvidence_sound (k : Nat) (w : TruthEvidence k) (t : RecursorTerm) :
    RootTerminates t := by
  cases k with
  | zero => exact (freeRecursor_no_directWhole ⟨w⟩).elim
  | succ k =>
    cases k with
    | zero => exact w.wellFounded.apply t
    | succ k =>
      cases k with
      | zero => exact freeRecursor_step_rev_wellFounded.apply t
      | succ k => exact w.down.apply t

theorem boundaryEvidence_sound (k : Nat) (w : BoundaryEvidence k) (t : RecursorTerm) :
    RootTerminates t := by
  cases k with
  | zero => exact (freeRecursor_no_directWhole ⟨w⟩).elim
  | succ k =>
    cases k with
    | zero => exact w.1.wellFounded.apply t
    | succ k =>
      cases k with
      | zero => exact freeRecursor_step_rev_wellFounded.apply t
      | succ k => exact w.down.apply t

def truthHierarchy : WitnessHierarchy RecursorTerm where
  W := fun k _ _ => TruthEvidence k
  accepts := fun {k P x} _ => P = RootTerminates
  sound := by
    intro k P x w h
    rw [h]
    exact truthEvidence_sound k w x

def boundaryHierarchy : WitnessHierarchy RecursorTerm where
  W := fun k _ _ => BoundaryEvidence k
  accepts := fun {k P x} _ => P = RootTerminates
  sound := by
    intro k P x w h
    rw [h]
    exact boundaryEvidence_sound k w x

theorem truthHierarchy_adequate_iff (k : Nat) (t : RecursorTerm) :
    truthHierarchy.hasAdequateAtDepth k RootTerminates t ↔ 1 ≤ k := by
  cases k with
  | zero =>
    constructor
    · rintro ⟨⟨w, _⟩⟩
      exact (freeRecursor_no_directWhole ⟨w⟩).elim
    · omega
  | succ k =>
    constructor
    · intro _; omega
    · intro _
      cases k with
      | zero => exact ⟨⟨importedWholeWitness, rfl⟩⟩
      | succ k =>
        cases k with
        | zero => exact ⟨⟨transformedCallWitness, rfl⟩⟩
        | succ k => exact ⟨⟨externalWitness, rfl⟩⟩

theorem boundaryHierarchy_adequate_iff (k : Nat) (t : RecursorTerm) :
    boundaryHierarchy.hasAdequateAtDepth k RootTerminates t ↔ 2 ≤ k := by
  cases k with
  | zero =>
    constructor
    · rintro ⟨⟨w, _⟩⟩
      exact (freeRecursor_no_directWhole ⟨w⟩).elim
    · omega
  | succ k =>
    cases k with
    | zero =>
      constructor
      · rintro ⟨⟨w, _⟩⟩
        exact (no_erasedCounterDecoder ⟨w.2⟩).elim
      · omega
    | succ k =>
      constructor
      · intro _; omega
      · intro _
        cases k with
        | zero => exact ⟨⟨transformedCallWitness, rfl⟩⟩
        | succ k => exact ⟨⟨externalWitness, rfl⟩⟩

noncomputable def kappaTruth (t : RecursorTerm) : Nat := by
  classical
  exact Nat.find (show ∃ k, truthHierarchy.hasAdequateAtDepth k RootTerminates t from
    ⟨1, (truthHierarchy_adequate_iff 1 t).mpr (by omega)⟩)

noncomputable def kappaBoundary (t : RecursorTerm) : Nat := by
  classical
  exact Nat.find (show ∃ k, boundaryHierarchy.hasAdequateAtDepth k RootTerminates t from
    ⟨2, (boundaryHierarchy_adequate_iff 2 t).mpr (by omega)⟩)

theorem freeRecursor_kappaTruth_eq_importedWhole (t : RecursorTerm) :
    kappaTruth t = 1 := by
  classical
  unfold kappaTruth
  apply Nat.le_antisymm
  · exact Nat.find_min' _ ((truthHierarchy_adequate_iff 1 t).mpr (by omega))
  · exact (truthHierarchy_adequate_iff _ t).mp
      (Nat.find_spec (show ∃ k, truthHierarchy.hasAdequateAtDepth k RootTerminates t from
        ⟨1, (truthHierarchy_adequate_iff 1 t).mpr (by omega)⟩))

theorem freeRecursor_kappaBoundary_eq_transformedCall (t : RecursorTerm) :
    kappaBoundary t = 2 := by
  classical
  unfold kappaBoundary
  apply Nat.le_antisymm
  · exact Nat.find_min' _ ((boundaryHierarchy_adequate_iff 2 t).mpr (by omega))
  · exact (boundaryHierarchy_adequate_iff _ t).mp
      (Nat.find_spec (show ∃ k, boundaryHierarchy.hasAdequateAtDepth k RootTerminates t from
        ⟨2, (boundaryHierarchy_adequate_iff 2 t).mpr (by omega)⟩))

theorem freeRecursor_truth_representationShiftBottleneck (t : RecursorTerm) :
    RepresentationShiftBottleneck truthHierarchy RootTerminates t 1 where
  property_holds := freeRecursor_step_rev_wellFounded.apply t
  no_witness_below := by
    intro j hj hw
    have := (truthHierarchy_adequate_iff j t).mp hw
    omega
  witness_at_k := (truthHierarchy_adequate_iff 1 t).mpr (by omega)

theorem freeRecursor_boundary_representationShiftBottleneck (t : RecursorTerm) :
    RepresentationShiftBottleneck boundaryHierarchy RootTerminates t 2 where
  property_holds := freeRecursor_step_rev_wellFounded.apply t
  no_witness_below := by
    intro j hj hw
    have := (boundaryHierarchy_adequate_iff j t).mp hw
    omega
  witness_at_k := (boundaryHierarchy_adequate_iff 2 t).mpr (by omega)

theorem truth_bottleneck_iff_depth_one (t : RecursorTerm) (k : Nat) :
    RepresentationShiftBottleneck truthHierarchy RootTerminates t k ↔ k = 1 := by
  constructor
  · intro h
    have hlow := (truthHierarchy_adequate_iff k t).mp h.witness_at_k
    by_contra hk
    exact h.no_witness_below 1 (by omega)
      (truthHierarchy_adequate_iff 1 t |>.mpr (by omega))
  · rintro rfl
    exact freeRecursor_truth_representationShiftBottleneck t

theorem boundary_bottleneck_iff_depth_two (t : RecursorTerm) (k : Nat) :
    RepresentationShiftBottleneck boundaryHierarchy RootTerminates t k ↔ k = 2 := by
  constructor
  · intro h
    have hlow := (boundaryHierarchy_adequate_iff k t).mp h.witness_at_k
    by_contra hk
    exact h.no_witness_below 2 (by omega)
      (boundaryHierarchy_adequate_iff 2 t |>.mpr (by omega))
  · rintro rfl
    exact freeRecursor_boundary_representationShiftBottleneck t

end OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorWitnessOrder
