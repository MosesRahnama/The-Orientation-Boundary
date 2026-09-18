import Mathlib

/-!
# Licensed abstract reduction systems

## Formal Scope

Scope tags record caller-declared metadata. They do not validate that a relation has the semantics named by its tag.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

/-- Whether a relation contracts only at the root or includes context closure. -/
inductive RelationLocation
  | root
  | context
  deriving DecidableEq, Repr

/-- The closure represented by a public relation surface. -/
inductive ClosureKind
  | oneStep
  | reflexiveTransitive
  deriving DecidableEq, Repr

/-- Whether the public relation exposes every edge or a licensed subrelation. -/
inductive AdmissionKind
  | full
  | guarded
  deriving DecidableEq, Repr

/-- The rewriting layer represented by an abstract system. -/
inductive RelationLayer
  | original
  | projected
  | dependencyPair
  deriving DecidableEq, Repr

/-- Audit metadata for a relation.  Each coordinate has a separate type so a
projected relation cannot silently become a dependency-pair relation. -/
structure RelationAuditScope where
  location : RelationLocation
  closure : ClosureKind
  admission : AdmissionKind
  layer : RelationLayer
  deriving DecidableEq, Repr

/-- A reduction system with an explicit audit scope. -/
structure ARS where
  Carrier : Type u
  step : Carrier -> Carrier -> Prop
  scope : RelationAuditScope

/-- An `n`-step path in an abstract reduction system. -/
inductive Steps (A : ARS.{u}) : Nat -> A.Carrier -> A.Carrier -> Prop where
  | zero (x : A.Carrier) : Steps A 0 x x
  | succ {n : Nat} {x y z : A.Carrier} :
      A.step x y -> Steps A n y z -> Steps A (n + 1) x z

/-- Concatenation preserves the sum of path lengths. -/
theorem Steps.append {A : ARS.{u}} {m n : Nat} {x y z : A.Carrier}
    (hxy : Steps A m x y) (hyz : Steps A n y z) :
    Steps A (m + n) x z := by
  induction hxy with
  | zero => simpa using hyz
  | @succ k a b c hab hbc ih =>
      convert Steps.succ hab (ih hyz) using 1
      omega

/-- A one-step simulation maps finite paths of the same length. -/
theorem Steps.map {A : ARS.{u}} {B : ARS.{v}} (f : A.Carrier -> B.Carrier)
    (hstep : forall {x y}, A.step x y -> B.step (f x) (f y)) {n : Nat}
    {x y : A.Carrier} (h : Steps A n x y) :
    Steps B n (f x) (f y) := by
  induction h with
  | zero a => exact Steps.zero (f a)
  | @succ k a b c hab hbc ih => exact Steps.succ (hstep hab) ih

/-- Reflexive-transitive reachability with a retained path-length witness. -/
def Reach (A : ARS.{u}) (x y : A.Carrier) : Prop :=
  exists n, Steps A n x y

/-- Every state reaches itself. -/
theorem reach_refl {A : ARS.{u}} (x : A.Carrier) : Reach A x x :=
  ⟨0, Steps.zero x⟩

/-- Every one-step edge is reachable. -/
theorem reach_step {A : ARS.{u}} {x y : A.Carrier} (h : A.step x y) :
    Reach A x y :=
  ⟨1, by simpa using Steps.succ h (Steps.zero y)⟩

/-- Reachability is transitive. -/
theorem reach_trans {A : ARS.{u}} {x y z : A.Carrier}
    (hxy : Reach A x y) (hyz : Reach A y z) : Reach A x z := by
  rcases hxy with ⟨m, hm⟩
  rcases hyz with ⟨n, hn⟩
  exact ⟨m + n, hm.append hn⟩

/-! ## Non-vacuity fixture -/

/-- Two states used by the reduction fixture. -/
inductive ChainNode
  | source
  | target
  deriving DecidableEq, Fintype, Repr

/-- The fixture has one genuine edge. -/
inductive ChainStep : ChainNode -> ChainNode -> Prop
  | descend : ChainStep .source .target

/-- A root, one-step, full, original reduction system with one edge. -/
def chainARS_fixture : ARS where
  Carrier := ChainNode
  step := ChainStep
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- The fixture edge gives a one-step path and a reachability witness. -/
theorem chainARS_reach_fixture : Reach chainARS_fixture .source .target :=
  reach_step ChainStep.descend

#check @Steps.append
#check @Steps.map
#check @reach_trans
#check chainARS_reach_fixture
#print axioms Steps.append
#print axioms Steps.map
#print axioms reach_trans
#print axioms chainARS_reach_fixture

end OperatorKO7.Meta.LicensedBoundaryCalculus
