import OperatorKO7.Meta.UUET.Probability.FiniteDistribution

set_option autoImplicit false

/-!
# Finite stochastic channels

Relation: a source outcome selects one normalized output law.
Closure: deterministic and identity channels remain finite stochastic channels.
Trust: kernel-only finite algebra.
Scope: classical finite Markov kernels; no quantum-channel transport.
-/

namespace OperatorKO7.Meta.UUET.Probability

/-- A finite stochastic channel represented by normalized rows. -/
structure Channel (α β : Type) [Fintype α] [Fintype β] where
  row : α -> FiniteDistribution β

namespace Channel

/-- A deterministic map as a stochastic channel. -/
def deterministic {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α -> β) : Channel α β where
  row := fun x => FiniteDistribution.pointMass (f x)

/-- Identity finite channel. -/
def identity (α : Type) [Fintype α] [DecidableEq α] : Channel α α :=
  deterministic id

@[simp] theorem deterministic_mass {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α -> β) (x : α) :
    ((deterministic f).row x).mass (f x) = 1 := by
  simp [deterministic]

theorem row_mass_le_one {α β : Type} [Fintype α] [Fintype β]
    (K : Channel α β) (x : α) (y : β) : (K.row x).mass y <= 1 :=
  FiniteDistribution.mass_le_one (K.row x) y

/-- Negative fixture: a stochastic row cannot assign mass above one. -/
theorem no_channel_row_mass_above_one {α β : Type} [Fintype α] [Fintype β]
    (K : Channel α β) (x : α) (y : β) : Not (1 < (K.row x).mass y) := by
  exact not_lt_of_ge (row_mass_le_one K x y)

end Channel

/-! Imported NameGate and TypeGate. -/
#check @FiniteDistribution.pointMass
#check @id
#check @Channel.row
#check @Channel.deterministic

#check @Channel.deterministic_mass
#check @Channel.row_mass_le_one
#check @Channel.no_channel_row_mass_above_one
#print axioms Channel.deterministic_mass
#print axioms Channel.row_mass_le_one
#print axioms Channel.no_channel_row_mass_above_one

end OperatorKO7.Meta.UUET.Probability
