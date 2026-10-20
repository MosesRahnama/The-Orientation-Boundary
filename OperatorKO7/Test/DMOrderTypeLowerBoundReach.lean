import OperatorKO7.Meta.DM_OrderType_LowerBound

namespace DMOrderTypeLowerBoundReach

open OperatorKO7.MetaDM

#check dmOrdEmbed_injective
#check dmOrdEmbed_eq_iff

example {m₁ m₂ : Multiset Nat} (h : dmOrdEmbed m₁ = dmOrdEmbed m₂) : m₁ = m₂ :=
  dmOrdEmbed_injective h

example {m₁ m₂ : Multiset Nat} : dmOrdEmbed m₁ = dmOrdEmbed m₂ ↔ m₁ = m₂ :=
  dmOrdEmbed_eq_iff

end DMOrderTypeLowerBoundReach
