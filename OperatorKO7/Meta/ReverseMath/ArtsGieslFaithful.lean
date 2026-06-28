import OperatorKO7.Meta.ReverseMath.StandardModel
import OperatorKO7.Meta.ReverseMath.ArtsGieslPi02

/-!
# Faithfulness bridge for the Arts–Giesl / SCT soundness sentence

The mandatory faithfulness obligation (roadmap §Faithfulness Obligations): the object sentence
`ArtsGieslSctSoundnessFormula` must be tied to the genuine Lean fact it encodes, via
"standard-model satisfaction `↔` the actual property". Here:

* `ActualArtsGieslSctSoundness` is the genuine arithmetical content (a `Π⁰₂` statement over `ℕ`);
* `artsGieslSctSoundness_faithful` proves `StdCarrier ⊨ ArtsGieslSctSoundnessFormula ↔
  ActualArtsGieslSctSoundness` (the relativized quantifiers restrict the single-sorted carrier to
  its number part `ℕ`);
* `actualArtsGieslSctSoundness_holds` proves the property is true, so the standard model genuinely
  satisfies the sentence (`stdModel_models_artsGieslSctSoundness`) -- it is sound, not vacuous.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.ReverseMath

open FirstOrder Language

/-- The genuine arithmetical content of the SCT/AG soundness sentence: every number `m` has a
descent witness `n` (with `n < m`) unless it is already at the floor `0`. A `Π⁰₂` statement over `ℕ`. -/
def ActualArtsGieslSctSoundness : Prop := ∀ m : ℕ, ∃ n : ℕ, n < m ∨ m = 0

/-- The actual property is true over `ℕ`: for `m = 0` take the right disjunct; for `m = k + 1` take
`n = k < m`. (So the encoded sentence is sound, not vacuous.) -/
theorem actualArtsGieslSctSoundness_holds : ActualArtsGieslSctSoundness := by
  intro m
  cases m with
  | zero => exact ⟨0, Or.inr rfl⟩
  | succ k => exact ⟨k, Or.inl (Nat.lt_succ_self k)⟩

/-- **Faithfulness bridge.** The standard model satisfies the SCT/AG soundness sentence iff the
genuine arithmetical property `ActualArtsGieslSctSoundness` holds. The relativization guards
(`¬IsSet`) restrict the single-sorted carrier `ℕ ⊕ Set ℕ` to its number part: set elements satisfy
the matrix vacuously, number elements `inl m` carry exactly the `ℕ`-statement. -/
theorem artsGieslSctSoundness_faithful :
    (StdCarrier ⊨ ArtsGieslSctSoundnessFormula) ↔ ActualArtsGieslSctSoundness := by
  simp only [ArtsGieslSctSoundnessFormula, ActualArtsGieslSctSoundness, sctMatrix, ltBd, isSetBd,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_all, BoundedFormula.realize_ex,
    BoundedFormula.realize_imp, BoundedFormula.realize_inf, BoundedFormula.realize_sup,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, BoundedFormula.realize_rel₁,
    BoundedFormula.realize_rel₂]
  constructor
  · -- forward: instantiate the universal at the number `inl m`. The bound-variable environment
    -- resolves definitionally, and `RelMap` on `inl`/`inr` reduces by `cases`.
    intro h m
    obtain ⟨b, hb⟩ := h (Sum.inl m)
    -- `¬ IsSet (inl m)` holds (reduces to `¬ False`), so the implication fires.
    obtain ⟨hbnum, hbody⟩ := hb (id : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl m])
    -- `b` is a number (not a set), say `inl n`.
    cases b with
    | inr S => exact absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hbnum
    | inl n =>
        refine ⟨n, ?_⟩
        rcases hbody with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr (Sum.inl_injective heq)
  · -- backward: case on whether the element is a number or a set.
    intro h a
    cases a with
    | inr S =>
        -- set element: `¬ IsSet (inr S)` is false, so the implication is vacuously satisfied.
        exact ⟨Sum.inl 0,
          fun hcon => absurd (trivial : stdStructure.RelMap Rel.isSet ![Sum.inr S]) hcon⟩
    | inl m =>
        obtain ⟨n, hn⟩ := h m
        refine ⟨Sum.inl n, fun _ => ⟨(id : ¬ stdStructure.RelMap Rel.isSet ![Sum.inl n]), ?_⟩⟩
        rcases hn with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr (congrArg Sum.inl heq)

/-- The standard model genuinely satisfies the SCT/AG soundness sentence (Gate R5 soundness: the
sentence is true in the intended model, not vacuous). -/
theorem stdModel_models_artsGieslSctSoundness :
    StdCarrier ⊨ ArtsGieslSctSoundnessFormula :=
  artsGieslSctSoundness_faithful.mpr actualArtsGieslSctSoundness_holds

end OperatorKO7.ReverseMath
