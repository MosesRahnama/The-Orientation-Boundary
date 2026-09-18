import OperatorKO7.Meta.UniqueNormalization.DecreasingSequenceMeasure

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @LevelKey
#check @LevelLabel.toKey
#check @levelLabel_toKey_lt_iff
#check @Unlabelled
#check @LPath
#check @LPath.refl
#check @LPath.cons
#check @LPath.trans
#check @LPath.snoc
#check @LPath.toStar
#check @exists_lPath_of_star
#check @AllBelow
#check @AllBelowEither
#check @exists_lPath_allBelow_of_star_stepBelow
#check @exists_lPath_allBelowEither_of_star_stepBelowEither
#check @removeBelow
#check @lexMax
#check @lexMax_nil
#check @lexMax_cons
#check @lexMax_singleton
#check @mem_lexMax_source
#check @lexMax_dm_lt_singleton_of_allBelow
#check @lexMax_dm_lt_pair_of_allBelowEither
#check @peakMeasure
#check @PeakMeasureLt
#check @peakMeasureLt_wellFounded

#print axioms LevelKey
#print axioms LevelLabel.toKey
#print axioms levelLabel_toKey_lt_iff
#print axioms Unlabelled
#print axioms LPath
#print axioms LPath.refl
#print axioms LPath.cons
#print axioms LPath.trans
#print axioms LPath.snoc
#print axioms LPath.toStar
#print axioms exists_lPath_of_star
#print axioms AllBelow
#print axioms AllBelowEither
#print axioms exists_lPath_allBelow_of_star_stepBelow
#print axioms exists_lPath_allBelowEither_of_star_stepBelowEither
#print axioms removeBelow
#print axioms lexMax
#print axioms lexMax_nil
#print axioms lexMax_cons
#print axioms lexMax_singleton
#print axioms mem_lexMax_source
#print axioms lexMax_dm_lt_singleton_of_allBelow
#print axioms lexMax_dm_lt_pair_of_allBelowEither
#print axioms peakMeasure
#print axioms PeakMeasureLt
#print axioms peakMeasureLt_wellFounded
