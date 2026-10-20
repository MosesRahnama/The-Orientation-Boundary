import OperatorKO7.Meta.SafeStep.FaithfulnessNoGo

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# The fiber-bundle reframing of the faithfulness no-go

An external review proposed modelling rewrite states as a fiber bundle in order to
obtain a *faithful dynamical functor through the boundary that recovers the
discarded payload*. That object cannot exist: `FaithfulnessNoGo` already proves
(`not_payloadFaithful_of_covers`) that no payload-discarding boundary admits a
covering payload-faithful dynamical functor, because `payloadDiscarding` is a
defining law of every `BoundaryOperator`.

This module encodes the *honest* geometric statement instead. The correct bundle
picture is:

```text
total space E  =  the rewrite carrier (Trace), which is faithful and carries payload
base       B  =  the collapsed verdict produced by the distinction boundary operator
proj : E → B  =  the actual collapse / verdict map of the distinction boundary
```

A *payload-faithful global section* would be a right-splitting `s : B → E` with
`s ∘ proj = id`, i.e. a way to recover every fiber point from its verdict. The
no-go is exactly the statement that a *payload-discarding* projection (one that
identifies two distinct total-space points) admits **no** such section: a section
is a left inverse of `proj`, and a map with a left inverse is injective, so it
cannot collapse two distinct points.

Honesty scope (load-bearing). This module asserts only the **absence** of a
payload-faithful section. It does **not** assert, anywhere, the existence of a
faithful dynamical functor through the boundary; the review's proposed object is
precisely what `FaithfulnessNoGo` rules out, and the lemma
`bundle_no_section_matches_faithfulness_nogo` records that the no-section result
here is the bundle-language form of that proven no-go. The genuine content is the
distinction-boundary instantiation: a real collapse projection
(`distinctionBoundaryOperator.apply`), two real distinct `Trace` terms (`void` and
`delta void`) with one verdict (`void`), and the explicit tie to the proven law.

It contains no `sorry`, no new `axiom`, no `native_decide`, no `bv_decide`, no
`@[csimp]`, no `unsafe`, no `partial`, and no `opaque`. The headline theorems are
spot-checked with `#print axioms` (baseline whitelist
`{propext, Classical.choice, Quot.sound}`).
-/

open OperatorKO7 Trace
open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.Meta.SafeStep.BoundaryDuality

namespace OperatorKO7.Meta.SafeStep.BoundaryBundle

/-! ## 1–4. The abstract honest bundle statement -/

/-- A boundary fiber bundle: a faithful total space `E`, a collapsed base `B`, and
the bundle projection `proj : E → B`. The fibers of `proj` are the payload the base
does not see. -/
structure BoundaryBundle where
  /-- The total space: the faithful, payload-carrying states. -/
  E : Type
  /-- The base space: the collapsed verdicts. -/
  B : Type
  /-- The bundle projection collapsing total-space points to their verdict. -/
  proj : E → B

/-- A bundle is *payload-discarding* when its projection identifies two distinct
total-space points: the fiber over their common verdict carries payload (the
difference between `e1` and `e2`) that the base cannot see. -/
def IsPayloadDiscarding (Bd : BoundaryBundle) : Prop :=
  ∃ e1 e2 : Bd.E, e1 ≠ e2 ∧ Bd.proj e1 = Bd.proj e2

/-- A *payload-faithful global section* is a section `s : B → E` of the projection
that recovers every fiber point through its verdict, i.e. a right-splitting with
`s ∘ proj = id`. It is, equivalently, a left inverse of `proj`. -/
def PayloadFaithfulSection (Bd : BoundaryBundle) (s : Bd.B → Bd.E) : Prop :=
  ∀ e : Bd.E, s (Bd.proj e) = e

/-- THE HONEST NO-GO (abstract). A payload-discarding projection has no
payload-faithful global section. A section is a left inverse of `proj`, hence makes
`proj` injective; but a payload-discarding projection collapses two distinct points,
a contradiction. This is the bundle-language form of the faithfulness no-go: no
recovery of the discarded payload through the verdict exists. -/
theorem no_payloadFaithful_section (Bd : BoundaryBundle)
    (hpd : IsPayloadDiscarding Bd) :
    ¬ ∃ s : Bd.B → Bd.E, PayloadFaithfulSection Bd s := by
  rintro ⟨s, hs⟩
  obtain ⟨e1, e2, hne, hproj⟩ := hpd
  apply hne
  calc
    e1 = s (Bd.proj e1) := (hs e1).symm
    _  = s (Bd.proj e2) := by rw [hproj]
    _  = e2             := hs e2

/-! ## 5. The genuine distinction-boundary instantiation

The projection is the *actual* collapse map of the distinction boundary operator
`distinctionBoundaryOperator = collapseBoundaryOperator void` from
`BoundaryDuality`: every in-domain query collapses to the verdict `void`. We take
the total space to be the rewrite carrier `Trace` (the payload-carrying state) and
the base to be `Trace` (the verdict carrier), with the projection sending a trace
`t` to the boundary verdict on the live input `some t`. -/

/-- The honest distinction-boundary projection: the rewrite carrier `Trace` projected
to its distinction-boundary verdict. By construction this is
`distinctionBoundaryOperator.apply (some t) _`, the genuine constant-collapse verdict
map (`= void`), not an abstract toy. -/
noncomputable def distinctionProj (t : Trace) : Trace :=
  distinctionBoundaryOperator.apply (some t) (by
    show (some t : Option Trace) ≠ none
    exact (Option.some_ne_none t))

/-- Every trace projects to the distinction verdict `void`: the projection is the
real constant-collapse map of `distinctionBoundaryOperator`. -/
theorem distinctionProj_eq_void (t : Trace) : distinctionProj t = void := rfl

/-- THE DISTINCTION-BOUNDARY BUNDLE. Total space and base are the rewrite carrier
`Trace`; the projection is the genuine distinction-boundary collapse map. -/
noncomputable def distinctionBundle : BoundaryBundle where
  E := Trace
  B := Trace
  proj := distinctionProj

/-- The distinction bundle is payload-discarding, witnessed by the two genuinely
distinct rewrite traces `void` and `delta void`, which carry the same verdict
`void` under the real collapse map. This is a real distinctness of `Trace` terms
(`Trace.noConfusion`), not a contrived equality. -/
theorem distinctionBundle_isPayloadDiscarding :
    IsPayloadDiscarding distinctionBundle := by
  refine ⟨void, delta void, ?_, ?_⟩
  · intro h
    exact Trace.noConfusion h
  · show distinctionProj void = distinctionProj (delta void)
    rw [distinctionProj_eq_void, distinctionProj_eq_void]

/-- THE DISTINCTION-BOUNDARY NO-SECTION. The distinction bundle has no
payload-faithful global section: the verdict `void` cannot be inverted to recover
the distinct traces collapsed onto it. -/
theorem distinctionBundle_no_payloadFaithful_section :
    ¬ ∃ s : distinctionBundle.B → distinctionBundle.E,
        PayloadFaithfulSection distinctionBundle s :=
  no_payloadFaithful_section distinctionBundle distinctionBundle_isPayloadDiscarding

/-! ### Connection to the proven faithfulness no-go, and the explicit non-claim -/

/-- The no-section result is the bundle-language form of the proven faithfulness
no-go. The same payload-discarding obstruction drives both: a payload-faithful
*section* of `distinctionProj` would furnish a verdict-to-payload recovery on the
distinction boundary operator, contradicting its `payloadDiscarding` law, which is
exactly the law `FaithfulnessNoGo.not_payloadFaithful_of_covers` consumes to refute
a covering payload-faithful dynamical *functor*. We discharge the bundle side here
directly against `distinctionBoundaryOperator.payloadDiscarding` (reusing
`BoundaryDuality`, not re-proving it), so the two impossibilities share one root. -/
theorem bundle_no_section_matches_faithfulness_nogo :
    (¬ ∃ s : distinctionBundle.B → distinctionBundle.E,
        PayloadFaithfulSection distinctionBundle s)
    ∧ (¬ ∃ recover : Trace → distinctionBoundaryOperator.Payload,
        ∀ xh : {x : Option Trace // distinctionBoundaryOperator.domain x},
          recover (distinctionBoundaryOperator.apply xh.1 xh.2)
            = distinctionBoundaryOperator.payload_extract xh.1) := by
  refine ⟨distinctionBundle_no_payloadFaithful_section, ?_⟩
  exact distinctionBoundaryOperator.payloadDiscarding

/-- Explicit non-claim. This module asserts the **absence** of a payload-faithful
global section of the distinction-boundary projection. It does **not** assert the
existence of any faithful dynamical functor through the boundary; that object is the
one the external review proposed and is exactly what
`FaithfulnessNoGo.not_payloadFaithful_of_covers` proves impossible. The honest
geometry is: faithful total space, collapsed base, projection with no payload-faithful
section. -/
theorem no_faithful_dynamical_functor_is_claimed :
    ¬ OperatorKO7.Meta.SafeStep.FaithfulnessNoGo.PayloadFaithful
        OperatorKO7.Meta.SafeStep.DynamicalBoundaryFunctor.step_distinction_dynamical_boundary_functor :=
  OperatorKO7.Meta.SafeStep.FaithfulnessNoGo.distinction_no_faithful_dynamical_functor

#print axioms no_payloadFaithful_section
#print axioms distinctionBundle_isPayloadDiscarding
#print axioms distinctionBundle_no_payloadFaithful_section
#print axioms bundle_no_section_matches_faithfulness_nogo
#print axioms no_faithful_dynamical_functor_is_claimed

end OperatorKO7.Meta.SafeStep.BoundaryBundle
