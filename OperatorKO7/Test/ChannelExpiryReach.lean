import OperatorKO7.Meta.LicensedBoundaryCalculus.ChannelExpiry

/-!
# Reach gate for the fourth license-expiry object

Paired `#check` and `#print axioms` for every public declaration of
`Meta/LicensedBoundaryCalculus/ChannelExpiry.lean`: the endogenizing dynamics,
the object and its two distinguished states, the link to
`license_expiry_iff_reachable_echo`, the two blocked transports, the inhabited
transport into role erasure, and the four-object bundle. Expected footprint is a
subset of `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.ChannelExpiryReach

open OperatorKO7.Meta.LicensedBoundaryCalculus.ChannelExpiry

/-! ## The endogenizing dynamics -/

#check @channelCollapseStep
#check @channelCollapseStep_target_diagonal
#check @echo_of_diagonal
#check @offDiagonal_of_exogenous

#print axioms channelCollapseStep
#print axioms channelCollapseStep_target_diagonal
#print axioms echo_of_diagonal
#print axioms offDiagonal_of_exogenous

/-! ## The object -/

#check @channel_issue_exogenous
#check @channel_consume_echo
#check @channel_consume_not_exogenous
#check @channelExpiry
#check @channelExpiry_issue_license_expires
#check @channel_consume_self_loop

#print axioms channel_issue_exogenous
#print axioms channel_consume_echo
#print axioms channel_consume_not_exogenous
#print axioms channelExpiry
#print axioms channelExpiry_issue_license_expires
#print axioms channel_consume_self_loop

/-! ## Transport verdicts -/

#check @no_hom_channel_eqW
#check @no_hom_channel_quote
#check @channelToRole
#check @channelToRole_diagonal
#check @homChannelRole
#check @hom_channel_role_nonempty

#print axioms no_hom_channel_eqW
#print axioms no_hom_channel_quote
#print axioms channelToRole
#print axioms channelToRole_diagonal
#print axioms homChannelRole
#print axioms hom_channel_role_nonempty

/-! ## Bundles -/

#check @four_live_expiry_witnesses
#check @channel_expiry_is_fourth_object

#print axioms four_live_expiry_witnesses
#print axioms channel_expiry_is_fourth_object

end OperatorKO7.Test.ChannelExpiryReach
