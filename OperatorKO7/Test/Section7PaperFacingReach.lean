import OperatorKO7.Meta.UniqueNormalization.DescendingClassUniqueness

/-!
# Reach and axiom gate for descending-class uniqueness and Section 7 paper-facing names

Every public declaration of `DescendingClassUniqueness.lean` has a paired
`#check @` and `#print axioms`. The Section 7 names listed in the dispatch are
already pinned by `Section7TightClosureReach`, `Section7FiberReductionReach`,
`UN79SameGraphClosureReach`, `Section7FinalInterfaceReach`, and
`UN79ChainClassificationReach`, so they are not repeated here.
-/

set_option autoImplicit false

#check @OperatorKO7.Meta.UniqueNormalization.SymbolOccurs
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolOccurs
#check @OperatorKO7.Meta.UniqueNormalization.SymbolOccurs.here
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolOccurs.here
#check @OperatorKO7.Meta.UniqueNormalization.SymbolOccurs.of_arg
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolOccurs.of_arg
#check @OperatorKO7.Meta.UniqueNormalization.extLt
#print axioms OperatorKO7.Meta.UniqueNormalization.extLt
#check @OperatorKO7.Meta.UniqueNormalization.wellFounded_extLt
#print axioms OperatorKO7.Meta.UniqueNormalization.wellFounded_extLt
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_extension_consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_extension_consistent
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_extension_consistent
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_extension_consistent
#check @OperatorKO7.Meta.UniqueNormalization.rhsSymbolsDescend_constructorTranslation_extendedTRS
#print axioms OperatorKO7.Meta.UniqueNormalization.rhsSymbolsDescend_constructorTranslation_extendedTRS
#check @OperatorKO7.Meta.UniqueNormalization.consistent_extSystem_of_rhsSymbolsDescend
#print axioms OperatorKO7.Meta.UniqueNormalization.consistent_extSystem_of_rhsSymbolsDescend
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_translation_rhsSymbolsDescend
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_translation_rhsSymbolsDescend
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_translation_rhsSymbolsDescend
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_translation_rhsSymbolsDescend
#check @OperatorKO7.Meta.UniqueNormalization.SymbolsSatisfy.destructorLabel_of_occurs
#print axioms OperatorKO7.Meta.UniqueNormalization.SymbolsSatisfy.destructorLabel_of_occurs
#check @OperatorKO7.Meta.UniqueNormalization.rhsSymbolsDescend_of_rhs_symbols_below_root
#print axioms OperatorKO7.Meta.UniqueNormalization.rhsSymbolsDescend_of_rhs_symbols_below_root
#check @OperatorKO7.Meta.UniqueNormalization.UNconv_of_rhs_symbols_below_root
#print axioms OperatorKO7.Meta.UniqueNormalization.UNconv_of_rhs_symbols_below_root
#check @OperatorKO7.Meta.UniqueNormalization.UNred_of_rhs_symbols_below_root
#print axioms OperatorKO7.Meta.UniqueNormalization.UNred_of_rhs_symbols_below_root
#check @OperatorKO7.Meta.UniqueNormalization.capacityLt
#print axioms OperatorKO7.Meta.UniqueNormalization.capacityLt
#check @OperatorKO7.Meta.UniqueNormalization.capacityLt_wf
#print axioms OperatorKO7.Meta.UniqueNormalization.capacityLt_wf
#check @OperatorKO7.Meta.UniqueNormalization.capacity_rhs_symbols_below_root
#print axioms OperatorKO7.Meta.UniqueNormalization.capacity_rhs_symbols_below_root
#check @OperatorKO7.Meta.UniqueNormalization.capacity_rhsSymbolsDescend
#print axioms OperatorKO7.Meta.UniqueNormalization.capacity_rhsSymbolsDescend
#check @OperatorKO7.Meta.UniqueNormalization.capacity_rhs_carries_symbol
#print axioms OperatorKO7.Meta.UniqueNormalization.capacity_rhs_carries_symbol
#check @OperatorKO7.Meta.UniqueNormalization.descendingClass_nonvacuous
#print axioms OperatorKO7.Meta.UniqueNormalization.descendingClass_nonvacuous
#check @OperatorKO7.Meta.UniqueNormalization.descendingClass_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.descendingClass_UNconv
#check @OperatorKO7.Meta.UniqueNormalization.descendingClass_excludes_ko7
#print axioms OperatorKO7.Meta.UniqueNormalization.descendingClass_excludes_ko7
