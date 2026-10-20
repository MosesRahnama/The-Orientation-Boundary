import OperatorKO7.Meta.GenericConfessionMove

namespace GenericConfessionMoveReach

open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.GenericConfessionMove.GenericConfessionMove

def toyVerdict (n : Nat) : Prop := n = 0

def toyMove : GenericConfessionMove Nat toyVerdict Unit where
  licenseWitness := ()
  sourceBarrier := toyVerdict
  Quotient := Nat
  projection := id
  residualObstruction := toyVerdict
  Certificate := Nat
  certificateOf := id
  verifier := toyVerdict
  verifier_sound := by
    intro q h
    exact h
  barrier_covers_residual := by
    intro x h
    exact h
  soundness := by
    intro x h
    exact h
  verdictSufficient := by
    intro x x' h
    simpa [toyVerdict] using congrArg (fun n => n = 0) h

def toyMoveAlias : GenericConfessionMove Nat toyVerdict Unit := toyMove

#check GenericConfessionMove
#check GenericConfessionMove.licenseWitness
#check GenericConfessionMove.sourceBarrier
#check GenericConfessionMove.Quotient
#check GenericConfessionMove.projection
#check GenericConfessionMove.residualObstruction
#check GenericConfessionMove.Certificate
#check GenericConfessionMove.certificateOf
#check GenericConfessionMove.verifier
#check GenericConfessionMove.verifier_sound
#check GenericConfessionMove.barrier_covers_residual
#check GenericConfessionMove.soundness
#check GenericConfessionMove.verdictSufficient
#check GenericConfessionMove.certificate_projects_residual
#check GenericConfessionMove.residual_projects_sourceBarrier
#check GenericConfessionMove.residual_implies_verdict
#check GenericConfessionMove.RefinementWitness
#check GenericConfessionMove.Refines
#check GenericConfessionMove.Refines.refl
#check GenericConfessionMove.Refines.trans
#check GenericConfessionMove.Refines.projection_eq_of_projection_eq
#check GenericConfessionMove.Refines.transport_verdict
#check GenericConfessionMove.HEquivalenceWitness
#check GenericConfessionMove.HEquivalent
#check GenericConfessionMove.HEquivalent.refl
#check GenericConfessionMove.HEquivalent.symm
#check GenericConfessionMove.HEquivalent.trans

example : toyMove.residualObstruction (toyMove.projection 0) := by
  rfl

example : toyMove.sourceBarrier 0 := by
  exact GenericConfessionMove.residual_projects_sourceBarrier toyMove rfl

example : toyVerdict 0 := by
  exact GenericConfessionMove.residual_implies_verdict toyMove rfl

example : GenericConfessionMove.Refines toyMove toyMove :=
  GenericConfessionMove.Refines.refl toyMove

example : GenericConfessionMove.HEquivalent toyMove toyMoveAlias := by
  exact GenericConfessionMove.HEquivalent.refl toyMove

example : toyVerdict 0 ↔ toyVerdict 0 := by
  exact GenericConfessionMove.Refines.transport_verdict
    (GenericConfessionMove.Refines.refl toyMove) rfl

end GenericConfessionMoveReach
