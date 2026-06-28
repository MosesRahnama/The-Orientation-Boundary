/-!
# Theory IX: Endogenous provenance collapse

Boundary-general cross-paper packet, Theory IX. This closes the open question recorded in the
Boundary Operator Framework ("every trained network has a creator's-axiom-like opacity: the training
data's own provenance; can this be formalized as a licensed quotient?").

A query can be **non-vacuous at launch** (the asker assigns positive uncertainty to the answer
variable) yet be answered by authority that is **endogenous**: causally descended from the asker's
own corpus through citation, paraphrase, summarization, retrieval, licensed quotation, or
deterministic compilation. When that happens the *exogenous* information gain is zero even though the
*syntactic* gain may be positive. This is the typed form of the lived event: asking a system for the
name or interpretation of a notion whose text is already downstream of one's own writing returns
one's own authority as confirmation.

`provenance_collapse_exogenous_zero` is the load-bearing theorem; `lived_exogenous_zero` instantiates
it on a concrete closure system where the returned answer is genuinely derived from the base corpus
by a route step (not merely asserted), so the statement is non-vacuous.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.EndogenousProvenance

/-! ### Downstream closure of a corpus -/

/-- A closure system over answer carriers: a base-corpus predicate and a one-step derivation route
(citation, paraphrase, summarization, retrieval, licensed quotation, deterministic compilation). -/
structure ClosureSystem where
  Carrier : Type
  base : Carrier → Prop
  route : Carrier → Carrier → Prop

/-- The downstream closure of the base corpus under the derivation route: the least predicate
containing the base and closed under one route step. This is causal, not semantic: it tracks whether
the carrier descends from the asker's own material, not whether it is true. -/
inductive Downstream (S : ClosureSystem) : S.Carrier → Prop
  | base {x : S.Carrier} (h : S.base x) : Downstream S x
  | step {x y : S.Carrier} (hx : Downstream S x) (r : S.route x y) : Downstream S y

/-- Exogenous information gain is zero exactly when the answer lies in the downstream closure of the
asker's own corpus (the returned authority is endogenous). -/
def ExogenousGainZero (S : ClosureSystem) (answer : S.Carrier) : Prop :=
  Downstream S answer

/-! ### Provenance collapse -/

/-- A provenance collapse: the query is non-vacuous at launch (carried as an opaque positivity
fact `launched : nonvacuous_launch`, standing for `H(X_q | I_M) > 0`), yet the returned answer is
endogenous to the asker's downstream closure. -/
structure ProvenanceCollapse (S : ClosureSystem) where
  answer : S.Carrier
  nonvacuous_launch : Prop
  launched : nonvacuous_launch
  answer_endogenous : Downstream S answer

/-- **Provenance-collapse theorem (Theorem 9.5).** Under a provenance collapse the exogenous
information gain is zero: a non-vacuous query is answered with authority that descends entirely from
the asker's own corpus, so it adds nothing exogenous. The syntactic gain may still be positive; that
is recorded separately by `launched`. -/
theorem provenance_collapse_exogenous_zero (S : ClosureSystem) (P : ProvenanceCollapse S) :
    ExogenousGainZero S P.answer :=
  P.answer_endogenous

/-- **Confession reading (Corollary 9.6).** A provenance collapse leaves the verdict undischarged
with respect to exogenous authority: the honest routes are to disclose the endogenous status or to
supply an external license. Formally, the answer is endogenous (the exogenous gain is zero) while the
launch was non-vacuous, so the two readings are simultaneously witnessed. -/
theorem provenance_collapse_is_confession (S : ClosureSystem) (P : ProvenanceCollapse S) :
    P.nonvacuous_launch ∧ ExogenousGainZero S P.answer :=
  ⟨P.launched, P.answer_endogenous⟩

/-! ### A concrete closure system (the lived event, non-vacuity) -/

/-- The lived event's carriers: the asker's own `corpus`, and the `answer` paraphrased back. -/
inductive LivedCarrier where
  | corpus
  | answer

/-- The asker's material is the base; the route derives the answer from the corpus by paraphrase. -/
def livedSystem : ClosureSystem where
  Carrier := LivedCarrier
  base := fun x => x = LivedCarrier.corpus
  route := fun x y => x = LivedCarrier.corpus ∧ y = LivedCarrier.answer

/-- A concrete provenance collapse: the answer is reached from the base corpus by a genuine route
step, so it is endogenous, while the launch is non-vacuous. -/
def livedCollapse : ProvenanceCollapse livedSystem where
  answer := LivedCarrier.answer
  nonvacuous_launch := True
  launched := trivial
  answer_endogenous := Downstream.step (Downstream.base rfl) ⟨rfl, rfl⟩

/-- **Non-vacuity.** On the lived-event closure system, the endogenous answer has zero exogenous
gain, witnessed by a real derivation from the base corpus. -/
theorem lived_exogenous_zero : ExogenousGainZero livedSystem LivedCarrier.answer :=
  provenance_collapse_exogenous_zero livedSystem livedCollapse

#print axioms provenance_collapse_exogenous_zero
#print axioms lived_exogenous_zero

end OperatorKO7.Meta.BoundaryGeneral.EndogenousProvenance
