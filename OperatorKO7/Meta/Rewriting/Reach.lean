import OperatorKO7.Meta.Rewriting.CriticalPairComplete
import OperatorKO7.Meta.DistinctionBoundary.CriticalPairLemmaKO7

set_option autoImplicit false

/-!
# Reach gate for the generic first-order Critical Pair Lemma library

Statement-adequacy gate (ROADMAP-01). Every headline of the `Meta/Rewriting`
library is reached here, and the load-bearing theorems carry an axiom audit. The
library proves: a sound, complete, and most-general first-order unifier; a sound
critical-pair construction; the full Huet biconditional (local confluence if and
only if every critical pair is joinable); confluence from strong normalization and
critical-pair joinability; and the KO7 instantiation that recovers the eqW-diagonal
obstruction from the generic machinery.
-/

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.DistinctionBoundary

-- Unification (sound, complete, most-general as data).
#check @unify
#check @unify_sound
#check @unify_complete
#check @unify_mostGeneral

-- Rewriting and critical pairs.
#check @criticalPairs
#check @criticalPairs_sound
#check @criticalPairs_complete

-- The Critical Pair Lemma and confluence.
#check @localConfluent_imp_cp_joinable
#check @cp_joinable_imp_localConfluent
#check @critical_pair_lemma
#check @confluent_of_cp_joinable_of_SN

-- KO7 instantiation: adequacy and the generic recovery of the eqW-diagonal obstruction.
#check @kernel_step_iff_rootStep_reify
#check @ko7_eqW_diagonal_is_generic_critical_pair
#check @ko7_unguarded_has_nonjoinable_critical_pair

-- Axiom audit on the load-bearing headlines (each a subset of the baseline whitelist).
#print axioms unify_mostGeneral
#print axioms critical_pair_lemma
#print axioms confluent_of_cp_joinable_of_SN
#print axioms ko7_unguarded_has_nonjoinable_critical_pair
