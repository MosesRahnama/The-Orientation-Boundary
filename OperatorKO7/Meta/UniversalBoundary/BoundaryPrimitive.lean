import OperatorKO7.Meta.UniversalBoundary.BoundaryClass

/-!
# Universal Boundary Calculus: the unifying boundary primitive

The boundary-general packet (Theories I-XIV) and the universal layer mechanize many boundary
phenomena, but the packet's own Global Conventions name the primitive they all share: a boundary is a
typed mismatch in which the verdict depends on a dimension the cheap observation language cannot retain.
This module mechanizes that primitive as one structure, `TypedBoundary`, and proves the single universal
law that subsumes every facet:

> at a boundary, the true verdict is NOT a function of the cheap observation.

Equivalently, no observation-only rule can decide the verdict; a licensed change of witness channel is
required. Every facet is an instance: the duplicating recursor under a whole-term observer (Theory III),
the provenance-vs-license loop (Theory II), and the Licensed Boundary Calculus machine itself (a cheap
confidence signal cannot decide what a checked certificate decides, which is U2). The `TypedMismatch`
carrier records the packet's four-part shape (payload, control, verdict, license) that the boundary
projects onto.

## Audit slots

```
Relation: not a rewriting relation; the unifying boundary primitive and its universal law.
Closure:  not applicable.
Trust:    baseline or none; the universal law is one finite argument; instances are decidable.
Scope:    TypedBoundary, verdict_not_observation_function, the TypedMismatch carrier, and three
          facet instances (recursor / provenance / machine) with the no-cheap-decision corollary.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

/-- The four-part typed-mismatch carrier the boundary-general packet names: a payload, a control
channel, a verdict language, and a license. Every boundary phenomenon projects onto this shape. -/
structure TypedMismatch where
  Payload : Type
  Control : Type
  Verdict : Type
  License : Type

/-- The unifying boundary primitive. A cheap observation `observe` identifies two states `s₁`, `s₂`
(`obs_eq`) whose true verdict differs (`verdict_ne`). This is the packet's boundary definition reduced
to its core: the verdict depends on a dimension the observation cannot retain. -/
structure TypedBoundary where
  State : Type
  Obs : Type
  Verdict : Type
  observe : State → Obs
  verdict : State → Verdict
  s₁ : State
  s₂ : State
  obs_eq : observe s₁ = observe s₂
  verdict_ne : verdict s₁ ≠ verdict s₂

namespace TypedBoundary

/-- **The universal boundary law.** At a boundary, the true verdict is not a function of the cheap
observation: there is no observation-only rule that decides the verdict. This single theorem is the
shared content of every boundary phenomenon in the framework; a licensed change of witness channel is
required to recover the verdict. -/
theorem verdict_not_observation_function (B : TypedBoundary) :
    ¬ ∃ f : B.Obs → B.Verdict, ∀ s : B.State, B.verdict s = f (B.observe s) := by
  rintro ⟨f, hf⟩
  apply B.verdict_ne
  rw [hf B.s₁, hf B.s₂, B.obs_eq]

/-- The typed-mismatch carrier of a boundary: payload = states, control = the observation channel,
verdict = the verdict language, license = the dimension the observation cannot name (here `Unit`, the
slot the confession license fills). -/
def toMismatch (B : TypedBoundary) : TypedMismatch :=
  { Payload := B.State, Control := B.Obs, Verdict := B.Verdict, License := Unit }

end TypedBoundary

/-! ## Facet instances: the recursor, provenance, and the machine are one boundary -/

/-- **Theory III, the duplicating recursor.** Two trace states with the SAME whole-term mass (the cheap
observation) but a DIFFERENT role coordinate (the deciding dimension), so the mass observer cannot decide
the verdict. -/
def recursorMassBoundary : TypedBoundary where
  State := Bool × Nat        -- (role coordinate, whole-term mass)
  Obs := Nat                 -- the whole-term mass observer: blind to the role
  Verdict := Bool            -- the admissible verdict depends on the role
  observe := fun s => s.2
  verdict := fun s => s.1
  s₁ := (true, 5)
  s₂ := (false, 5)           -- identical mass 5, opposite role
  obs_eq := rfl
  verdict_ne := by decide

/-- **Theory II, provenance vs license.** Two responses returning the SAME source span (the cheap
observation) but differing in whether the off-span external license is present (the deciding dimension),
so the span alone cannot license the verdict. -/
def provenanceBoundary : TypedBoundary where
  State := Bool              -- whether the off-span external license is present
  Obs := Unit                -- the source span: identical, sees the span not the license
  Verdict := Bool            -- the verdict's admissibility depends on the license
  observe := fun _ => ()
  verdict := fun licensed => licensed
  s₁ := true
  s₂ := false
  obs_eq := rfl
  verdict_ne := by decide

/-- **The Licensed Boundary Calculus machine itself (U2).** Two inputs with the SAME cheap confidence
signal (the observation) but differing in whether a checked certificate is present (the deciding
dimension), so confidence cannot decide what the certificate decides. This places the universal
contract's own no-unsupported-yes guarantee inside the boundary primitive. -/
def machineBoundary : TypedBoundary where
  State := Bool              -- whether a checker-accepted certificate is present
  Obs := Unit                -- the cheap confidence signal: identical, blind to the certificate
  Verdict := Bool            -- emitted as a positive verdict or not
  observe := fun _ => ()
  verdict := fun hasCert => hasCert
  s₁ := true
  s₂ := false
  obs_eq := rfl
  verdict_ne := by decide

/-- Every facet inherits the universal law: at each, the verdict is not an observation-only function. -/
theorem all_facets_obey_universal_law :
    (¬ ∃ f : recursorMassBoundary.Obs → recursorMassBoundary.Verdict,
        ∀ s, recursorMassBoundary.verdict s = f (recursorMassBoundary.observe s))
      ∧ (¬ ∃ f : provenanceBoundary.Obs → provenanceBoundary.Verdict,
          ∀ s, provenanceBoundary.verdict s = f (provenanceBoundary.observe s))
      ∧ (¬ ∃ f : machineBoundary.Obs → machineBoundary.Verdict,
          ∀ s, machineBoundary.verdict s = f (machineBoundary.observe s)) :=
  ⟨TypedBoundary.verdict_not_observation_function recursorMassBoundary,
   TypedBoundary.verdict_not_observation_function provenanceBoundary,
   TypedBoundary.verdict_not_observation_function machineBoundary⟩

-- Axiom audit (Rule W16: recorded for the build log).
#print axioms TypedBoundary.verdict_not_observation_function
#print axioms all_facets_obey_universal_law

end OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
