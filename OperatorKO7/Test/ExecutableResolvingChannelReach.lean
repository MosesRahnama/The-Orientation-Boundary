import OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

set_option autoImplicit false

namespace OperatorKO7.Test.ExecutableResolvingChannelReach

/-! Current public source surface, including generated structure projections and inductive constructors, for supervisor validation. -/

#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.mk
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.items
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.nodup
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.complete
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.toFintype
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues_nodup
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.target_mem_orderedFiberValues
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.localRank
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.localRank_lt_fiberLength
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.toFin?
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.toFin?_some_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues_toFinset
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues_length
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.alphabetSize
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.localRank_lt_alphabetSize
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode?
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode?_isSome
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decode?
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decode_localRank
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decode_encode
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode_resolving
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode_licensed
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode_alphabet_optimal
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.no_smaller_fin_channel
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.optimal_fixedLength_bits
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.alphabetSize_enumeration_independent
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.fixedBitWidth
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.codeToBits
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.bitsToCode?
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.bitsToCode?_codeToBits
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encodeBits?
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decodeBits?
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decodeBits_encodeBits
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.fixedBitWidth_eq_fiberCodeDeficit
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.fixed_channel_stabilizes_at_image_bound
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizationStage
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizationStage_eq_image_bound
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizedEncoder
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizedEncoder_licensed
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizedEncoder_permanent
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.permanent_channel_capacity_at_stabilization
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.threeValueEnumeration
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.three_values_require_three_symbols
#check @OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.three_values_require_two_bits

#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.mk
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.items
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.nodup
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.complete
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.Enumeration.toFintype
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues_nodup
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.target_mem_orderedFiberValues
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.localRank
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.localRank_lt_fiberLength
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.toFin?
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.toFin?_some_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues_toFinset
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.orderedFiberValues_length
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.alphabetSize
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.localRank_lt_alphabetSize
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode?
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode?_isSome
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decode?
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decode_localRank
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decode_encode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode_resolving
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode_licensed
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encode_alphabet_optimal
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.no_smaller_fin_channel
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.optimal_fixedLength_bits
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.alphabetSize_enumeration_independent
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.fixedBitWidth
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.codeToBits
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.bitsToCode?
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.bitsToCode?_codeToBits
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.encodeBits?
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decodeBits?
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.decodeBits_encodeBits
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.fixedBitWidth_eq_fiberCodeDeficit
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.fixed_channel_stabilizes_at_image_bound
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizationStage
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizationStage_eq_image_bound
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizedEncoder
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizedEncoder_licensed
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.stabilizedEncoder_permanent
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.permanent_channel_capacity_at_stabilization
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.threeValueEnumeration
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.three_values_require_three_symbols
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel.three_values_require_two_bits
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel

example :
    encode? threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x) 2 =
      some ⟨2, by decide⟩ := by decide

example :
    decode? threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x)
      () ⟨2, by decide⟩ = some 2 := by decide

example :
    decode? threeValueEnumeration (fun _ : Fin 3 => false) (fun x => x)
      true ⟨0, by decide⟩ = none := by decide

example :
    decode? threeValueEnumeration (fun x : Fin 3 => decide (x = 0)) (fun x => x)
      true ⟨1, by decide⟩ = none := by decide

example :
    let E : Enumeration Empty :=
      { items := [], nodup := by simp, complete := by intro x; exact nomatch x }
    letI := E.toFintype
    alphabetSize E (fun _ : Empty => ()) (fun _ : Empty => ()) = 0 := by decide

example :
    Nat.clog 2 (alphabetSize threeValueEnumeration
      (fun _ : Fin 3 => ()) (fun x => x)) = 2 := by
  exact three_values_require_two_bits

example : stabilizationStage threeValueEnumeration (fun x : Fin 3 => x) = 2 := by
  decide

example : stabilizationStage threeValueEnumeration (fun _ : Fin 3 => ()) = 0 := by
  decide

example :
    (stabilizedEncoder threeValueEnumeration id (fun _ : Fin 3 => ()) id 2).val = 2 := by
  decide

example :
    bitsToCode? threeValueEnumeration (fun _ : Fin 3 => ()) id
      (BitVec.ofNat _ 3) = none := by
  change toFin? 3 (3 % 2 ^ Nat.clog 2 3) = none
  rw [show Nat.clog 2 3 = 2 from three_values_require_two_bits]
  decide

example :
    decodeBits? threeValueEnumeration (fun _ : Fin 3 => ()) id ()
      (codeToBits threeValueEnumeration (fun _ : Fin 3 => ()) id ⟨2, by decide⟩) = some 2 := by
  decide

end OperatorKO7.Test.ExecutableResolvingChannelReach
