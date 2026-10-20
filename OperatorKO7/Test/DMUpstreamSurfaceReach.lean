import OperatorKO7.Meta.DM_UpstreamSurface

namespace DMUpstreamSurfaceReach

open OperatorKO7.MetaDM
open OperatorKO7.MetaDMUpstream

#check DMOrderTypeUpstreamSurface
#check dmOrderTypeUpstreamSurface_holds
#check dmOrder_strictMono
#check dmOrder_reflects
#check dmOrder_injective
#check dmOrder_lt_opow_omega
#check dmOrder_exact_type

example {m₁ m₂ : Multiset Nat} (h : dmOrdEmbed m₁ = dmOrdEmbed m₂) : m₁ = m₂ :=
  dmOrder_injective h

end DMUpstreamSurfaceReach
