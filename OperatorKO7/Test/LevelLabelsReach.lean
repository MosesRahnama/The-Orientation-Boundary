import OperatorKO7.Meta.UniqueNormalization.LevelLabels

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @LevelLabel
#check @LevelLabel.mk
#check @LevelLabel.conditionLevel
#check @LevelLabel.unifierRank
#check @LevelLabel.toPair
#check @LevelLabelLt
#check @levelLabelLt_iff
#check @LevelLabelLt.of_conditionLevel_lt
#check @LevelLabelLt.of_unifierRank_lt
#check @levelLabelLt_wellFounded
#check @BelowEither
#check @BelowEither.of_left
#check @BelowEither.of_right

#print axioms LevelLabel
#print axioms LevelLabel.mk
#print axioms LevelLabel.conditionLevel
#print axioms LevelLabel.unifierRank
#print axioms LevelLabel.toPair
#print axioms LevelLabelLt
#print axioms levelLabelLt_iff
#print axioms LevelLabelLt.of_conditionLevel_lt
#print axioms LevelLabelLt.of_unifierRank_lt
#print axioms levelLabelLt_wellFounded
#print axioms BelowEither
#print axioms BelowEither.of_left
#print axioms BelowEither.of_right
