import OperatorKO7.Meta.ReverseMath.NewmanRCA0Upper

/-!
# Π¹₁ calibration of bare Newman

Packages the compiled facts: the bare-Newman sentence is `Π¹₁`, it holds in the
standard model, it is consistent with the RCA₀ basic fragment, and recorded
critical-pair joinability is quantifier-free.

Trust: kernel-only. No `sorry`/`admit`/`axiom`/`native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ReverseMath.BareNewmanPi11Calibration

open OperatorKO7.ReverseMath
open FirstOrder Language

/-- The compiled Π¹₁ calibration of bare Newman. -/
theorem bareNewman_pi11_calibration :
    IsPi11Set newmanSentence ∧
    (StdCarrier ⊨ newmanSentence) ∧
    (insert newmanSentence rca0BasicAxioms).IsSatisfiable ∧
    (∀ a b : L2.Term Empty, (cpJoinabilitySentence a b).IsQF) :=
  ⟨newmanSentence_isPi11, stdModel_newmanSentence, rca0Basic_consistent_with_newman,
    fun a b => cpJoinability_isLow a b⟩

end OperatorKO7.Meta.ReverseMath.BareNewmanPi11Calibration
