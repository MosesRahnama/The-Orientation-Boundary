import OperatorKO7.Meta.BoundaryObserver.EqualityRepairChecker
import OperatorKO7.Meta.BoundaryObserver.SoundExtensionIncompleteness
import OperatorKO7.Meta.BoundaryObserver.GodelPairSideSymbol
import OperatorKO7.Meta.BoundaryObserver.HaltingTerminalGap

/-!
# The Gödel sentence of the repaired checker and the repaired provability boundary

Manuscript: Theorem `thm:godel-equality-repair` and Corollary `cor:godel-equality-repair` of the
Observation-Boundary Principle.

The proof relation `proofRelE` of `T_E` is primitive recursive and defines `T_E`-provability, and
`T_E` is sound on `ℕ`, so the incompleteness theorem for sound primitive-recursive proof predicates
gives a sentence `γ_E` true on `ℕ` exactly when `T_E` does not prove it, with neither `γ_E` nor its
negation provable. The pair `γ_E`, `¬ γ_E` is then a collision of the provability record of `T_E`
for standard truth: the lift-or-refuse consequences, the side-symbol criterion and the invisible
transposition hold as for the base checker, and the fair binary label carries one bit.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.EqualityRepairGodel

open OperatorKO7.Meta.DistinctionBoundary.GodelArith
open OperatorKO7.Meta.DistinctionBoundary.GodelObserverCollision
open OperatorKO7.Meta.BoundaryObserver.EqualityRepair
open OperatorKO7.Meta.BoundaryObserver.EqualityRepairChecker
open OperatorKO7.Meta.BoundaryObserver.SoundExtensionIncompleteness
open OperatorKO7.Meta.OperationalInexpressibility

/-- **The Gödel sentence of `T_E`**, a sentence with no free variable. -/
theorem equality_repair_godel_sentence :
    ∃ γE : Formula, IsSentence γE ∧ (evalForm env0 γE ↔ ¬ ProvableE γE) ∧ ¬ ProvableE γE ∧
      ¬ ProvableE (Formula.not γE) := by
  obtain ⟨γ, h0, h1, h2, h3⟩ := sound_primrec_incompleteness proofRelE proofRelE_primrec
    (fun φ h => provableE_sound ((exists_proofRelE_iff φ).1 h) env0)
  refine ⟨γ, h0, ?_, ?_, ?_⟩
  · rw [← exists_proofRelE_iff]
    exact h1
  · rw [← exists_proofRelE_iff]
    exact h2
  · rw [← exists_proofRelE_iff]
    exact h3

/-- **Equality repair and semantic incompleteness.** The repaired checker `T_E` extends `T_0`, has
a primitive-recursive proof relation defining its provability, is sound on `ℕ`, proves exactly the
true closed equations, and has a sentence `γ_E` true on `ℕ` exactly when unprovable, with neither
`γ_E` nor `¬ γ_E` provable; every sound primitive-recursive proof predicate has such a sentence. -/
theorem godel_equality_repair :
    (∀ φ, Provable φ → ProvableE φ) ∧
    Primrec₂ proofRelE ∧
    (∀ φ, (∃ n, proofRelE n (encodeFormula φ) = true) ↔ ProvableE φ) ∧
    (∀ φ, ProvableE φ → ∀ env, evalForm env φ) ∧
    (∀ s t : Term, isClosedTerm s = true → isClosedTerm t = true →
      (ProvableE (Formula.eq s t) ↔ evalTerm env0 s = evalTerm env0 t)) ∧
    (∃ γE : Formula, IsSentence γE ∧ (evalForm env0 γE ↔ ¬ ProvableE γE) ∧ ¬ ProvableE γE ∧
      ¬ ProvableE (Formula.not γE)) ∧
    (∀ prf : ℕ → ℕ → Bool, Primrec₂ prf → (∀ φ, ProvBy prf φ → evalForm env0 φ) →
      ∃ γ : Formula, IsSentence γ ∧ (evalForm env0 γ ↔ ¬ ProvBy prf γ) ∧ ¬ ProvBy prf γ ∧
        ¬ ProvBy prf (Formula.not γ)) :=
  ⟨fun _ h => provable_to_provableE h, proofRelE_primrec, exists_proofRelE_iff,
    fun _ h env => provableE_sound h env, fun _ _ hs ht => closed_eq_iff hs ht,
    equality_repair_godel_sentence, sound_primrec_incompleteness⟩

/-- A Gödel sentence of `T_E`. -/
noncomputable def gammaE : Formula := Classical.choose equality_repair_godel_sentence

theorem gammaE_spec : IsSentence gammaE ∧ (evalForm env0 gammaE ↔ ¬ ProvableE gammaE) ∧
    ¬ ProvableE gammaE ∧ ¬ ProvableE (Formula.not gammaE) :=
  Classical.choose_spec equality_repair_godel_sentence

/-- The provability record of `T_E`. -/
def provabilityObserverE (φ : Formula) : Prop := ProvableE φ

theorem gammaE_true : truthTarget gammaE := gammaE_spec.2.1.2 gammaE_spec.2.2.1

/-- **The repaired collision.** -/
theorem gammaE_collision :
    DirectGrammarBoundary.OperationallyInexpressibleAt provabilityObserverE truthTarget
      gammaE (Formula.not gammaE) := by
  refine ⟨?_, ?_⟩
  · exact propext ⟨fun h => absurd h gammaE_spec.2.2.1, fun h => absurd h gammaE_spec.2.2.2⟩
  · intro h
    exact (Eq.mp h gammaE_true) gammaE_true

/-- The pair of the repaired sentence and its negation. -/
def gammaEPair : Set Formula := {gammaE, Formula.not gammaE}

theorem gammaE_side_symbol_iff {C : Type} (s : Formula → C) :
    LiftOrRefuse.LicensedOn gammaEPair
        (Confusability.augmentObserver provabilityObserverE s) truthTarget ↔
      s gammaE ≠ s (Formula.not gammaE) := by
  constructor
  · intro hlic
    rcases LiftOrRefuse.collision_lifted_or_refused gammaE_collision s hlic with hl | hr | hsep
    · exact False.elim (hl (by simp [gammaEPair]))
    · exact False.elim (hr (by simp [gammaEPair]))
    · exact hsep
  · intro hsep x hx y hy hObs
    simp only [gammaEPair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · rfl
      · exact False.elim (hsep (congrArg Prod.snd hObs))
    · rcases hy with rfl | rfl
      · exact False.elim (hsep (congrArg Prod.snd hObs).symm)
      · rfl

/-- A formula of the checker's language represents `T_E`-provability in `ℕ`. -/
theorem exists_bewE :
    ∃ Bew : Formula → Formula, ∀ φ, evalForm env0 (Bew φ) ↔ ProvableE φ := by
  obtain ⟨φI, hI⟩ := PrimrecDefinability.definable_of_primrec (prfInd_primrec proofRelE_primrec)
    53 54 (le_refl _) (by decide)
  refine ⟨fun φ => substNum (bewForm φI) (encodeFormula φ), fun φ => ?_⟩
  rw [evalForm_substNum, bewForm_spec hI, ← exists_proofRelE_iff]
  simp only [envUpdate, if_true]

/-- **The consistency collision of `T_E`.** For a formula `Bew` representing `T_E`-provability in
`ℕ`, and under the formalized first theorem `⊢_E Con_E → γ_E` that the derivability conditions
supply, the consistency sentence `Con_E = ¬ Bew(⊥)` and its negation are a second collision of the
provability record of `T_E` for standard truth. -/
theorem consistency_collision_E (Bew : Formula → Formula)
    (hRep : ∀ φ, evalForm env0 (Bew φ) ↔ ProvableE φ)
    (hImp : ProvableE (Formula.imp (Formula.not (Bew falsum)) gammaE)) :
    DirectGrammarBoundary.OperationallyInexpressibleAt provabilityObserverE truthTarget
      (Formula.not (Bew falsum)) (Formula.not (Formula.not (Bew falsum))) := by
  have hCon : truthTarget (Formula.not (Bew falsum)) := by
    intro h
    exact provableE_consistent ((hRep falsum).1 h)
  have hnp : ¬ ProvableE (Formula.not (Bew falsum)) := fun h =>
    gammaE_spec.2.2.1 (pE_mp hImp h)
  have hnn : ¬ ProvableE (Formula.not (Formula.not (Bew falsum))) := fun h =>
    (provableE_sound h env0) hCon
  refine ⟨propext ⟨fun h => absurd h hnp, fun h => absurd h hnn⟩, fun h => ?_⟩
  exact (Eq.mp h hCon) hCon

/-- **The repaired provability boundary.** The sentence `γ_E` and its negation are a collision of
the provability record of `T_E` for standard truth, with two maximal licensed singletons and no
greatest licensed set, the side-symbol criterion and the invisible transposition; under the
formalized first theorem the consistency sentence of `T_E` and its negation are a second collision;
the fair binary label carries one bit. -/
theorem godel_equality_repair_corollary :
    DirectGrammarBoundary.OperationallyInexpressibleAt provabilityObserverE truthTarget
      gammaE (Formula.not gammaE) ∧
    (((∃ S : Set Formula,
          LiftOrRefuse.MaximalLicensedOn S provabilityObserverE truthTarget ∧
          gammaE ∈ S ∧ Formula.not gammaE ∉ S) ∧
      ∃ T : Set Formula,
          LiftOrRefuse.MaximalLicensedOn T provabilityObserverE truthTarget ∧
          Formula.not gammaE ∈ T ∧ gammaE ∉ T) ∧
      ¬ ∃ G : Set Formula,
          LiftOrRefuse.LicensedOn G provabilityObserverE truthTarget ∧
          ∀ S : Set Formula, LiftOrRefuse.LicensedOn S provabilityObserverE truthTarget → S ⊆ G) ∧
    (∀ (C : Type) (s : Formula → C),
      LiftOrRefuse.LicensedOn gammaEPair
        (Confusability.augmentObserver provabilityObserverE s) truthTarget ↔
      s gammaE ≠ s (Formula.not gammaE)) ∧
    Equiv.swap gammaE (Formula.not gammaE) ∈
      LicenseStabilizer.licenseStabilizer provabilityObserverE ∧
    (∃ Bew : Formula → Formula, ∀ φ, evalForm env0 (Bew φ) ↔ ProvableE φ) ∧
    (∀ Bew : Formula → Formula, (∀ φ, evalForm env0 (Bew φ) ↔ ProvableE φ) →
      ProvableE (Formula.imp (Formula.not (Bew falsum)) gammaE) →
      DirectGrammarBoundary.OperationallyInexpressibleAt provabilityObserverE truthTarget
        (Formula.not (Bew falsum)) (Formula.not (Formula.not (Bew falsum)))) ∧
    ProtocolResolution.entropy (ProtocolResolution.binaryPrior (1 / 2)) = 1 :=
  ⟨gammaE_collision,
    ⟨LiftOrRefuse.maximal_refusals_of_collision gammaE_collision,
      LiftUniversalProperty.no_greatest_licensedOn_of_collision gammaE_collision⟩,
    fun _ s => gammaE_side_symbol_iff s,
    OperatorKO7.Meta.BoundaryGeneral.TwoVoidBoundary.swap_mem_licenseStabilizer
      provabilityObserverE gammaE_collision.1,
    exists_bewE,
    fun Bew hRep hImp => consistency_collision_E Bew hRep hImp,
    HaltingTerminalGap.fair_entropy⟩

end OperatorKO7.Meta.BoundaryObserver.EqualityRepairGodel
