import OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.UniversalGuardCompletion

open OperatorKO7.Meta.SafeStep.GenericDiagonalFork
open OperatorKO7.Meta.SafeStep.DistinctionWitnessBoundary

universe u
variable {T : Type u}

def CanonicalGuarded (S : DiagonalForkSchema T) (x y : T) : Prop :=
  (∃ a, x = S.E a a ∧ y = S.Z) ∨
    ∃ a b, a ≠ b ∧ x = S.E a b ∧ y = S.D a b

structure GuardedCompletion
    (S : DiagonalForkSchema T) (Rg : T -> T -> Prop) : Prop where
  sub_raw : ∀ {x y}, Rg x y -> S.R x y
  keep_refl : ∀ a, Rg (S.E a a) S.Z
  keep_offdiag_diff : ∀ {a b}, a ≠ b -> Rg (S.E a b) (S.D a b)
  refuse_diag_diff : ∀ a, ¬ Rg (S.E a a) (S.D a a)
  only_canonical : ∀ {x y}, Rg x y -> CanonicalGuarded S x y

def canonicalRelation (S : DiagonalForkSchema T) : T -> T -> Prop :=
  CanonicalGuarded S

theorem guardedCompletion_subset_canonical
    {S : DiagonalForkSchema T} {Rg : T -> T -> Prop}
    (H : GuardedCompletion S Rg) :
    ∀ {x y}, Rg x y -> canonicalRelation S x y :=
  H.only_canonical

theorem canonical_keeps_reflexive
    (S : DiagonalForkSchema T) (a : T) :
    canonicalRelation S (S.E a a) S.Z :=
  Or.inl ⟨a, rfl, rfl⟩

theorem canonical_keeps_offdiag
    (S : DiagonalForkSchema T) {a b : T} (h : a ≠ b) :
    canonicalRelation S (S.E a b) (S.D a b) :=
  Or.inr ⟨a, b, h, rfl, rfl⟩

theorem canonical_refuses_diag_diff
    (S : DiagonalForkSchema T) (a : T) (hZD : S.Z ≠ S.D a a)
    (diag_reflect : ∀ {c d}, S.E c d = S.E a a -> c = d) :
    ¬ (canonicalRelation S (S.E a a) (S.D a a)) := by
  intro h
  rcases h with h | h
  · rcases h with ⟨c, hsrc, htgt⟩
    exact hZD htgt.symm
  · rcases h with ⟨c, d, hne, hsrc, htgt⟩
    have : c = d := diag_reflect hsrc.symm
    exact hne this

#print axioms guardedCompletion_subset_canonical
#print axioms canonical_keeps_reflexive
#print axioms canonical_keeps_offdiag
#print axioms canonical_refuses_diag_diff

end OperatorKO7.Meta.SafeStep.UniversalGuardCompletion
