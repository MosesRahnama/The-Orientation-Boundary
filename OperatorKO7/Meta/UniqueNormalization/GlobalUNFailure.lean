import OperatorKO7.Meta.UniqueNormalization.Fence

/-!
# Global failure object for UN=

`UNconv R` says that every pair of convertible normal forms is equal. Its exact
failure object is therefore finite data: two normal forms, a conversion between
them, and a proof that they are distinct.

This module makes that data first-class and proves the exact equivalence

`¬ UNconv R ↔ Nonempty (GlobalUNFailure R)`.

The KO7 `eqW(void,void)` diagonal supplies a concrete instance whose two terminal
normal forms are `void` and `integrate(void)`. This welds the local diagonal fork
to global failure of unique normal forms without claiming the false converse
that every global UN= failure must arise from a one-step peak.

Relation: `conv R`, the equivalence closure of contextual rewriting.
Closure: conversion closure already built into `conv`.
Strategy: full rewriting.
Property: failure of `UNconv` / UN=.
Trust: kernel checked; classical witness extraction from a negated universal is
used only in the `¬UNconv → Nonempty` direction.
Scope: arbitrary first-order TRSs on the live Unique Normalization carrier.
Does not prove: that every failure contains a non-joinable one-step peak.
Non-vacuity: `ko7DiagonalFailure` is an explicit inhabitant.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.GlobalFailure

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization

universe u v

variable {sigma : Type u} {nu : Type v}

/-- Proof-relevant data witnessing failure of unique normal forms with respect
to conversion. -/
structure GlobalUNFailure (R : TRS sigma nu) : Type (max u v) where
  left : Term sigma nu
  right : Term sigma nu
  leftNormal : NormalForm R left
  rightNormal : NormalForm R right
  convertible : conv R left right
  distinct : left ≠ right

namespace GlobalUNFailure

/-- Every explicit global failure object refutes UN=. -/
theorem not_UNconv {R : TRS sigma nu} (f : GlobalUNFailure R) : ¬ UNconv R := by
  intro hun
  exact f.distinct (hun f.left f.right f.leftNormal f.rightNormal f.convertible)

/-- A global failure object is exactly the usual four-part witness hidden inside
`¬UNconv`: two normal forms, a conversion, and disequality. -/
theorem exists_data {R : TRS sigma nu} (f : GlobalUNFailure R) :
    ∃ s t, NormalForm R s ∧ NormalForm R t ∧ conv R s t ∧ s ≠ t :=
  ⟨f.left, f.right, f.leftNormal, f.rightNormal, f.convertible, f.distinct⟩

end GlobalUNFailure

/-- Negating the universal UN= property is exactly existence of distinct
convertible normal forms. The reverse direction is constructive; the forward
direction uses classical witness extraction from a negated dependent universal. -/
theorem not_UNconv_iff_exists_distinct_convertible_normalForms (R : TRS sigma nu) :
    ¬ UNconv R ↔
      ∃ s t, NormalForm R s ∧ NormalForm R t ∧ conv R s t ∧ s ≠ t := by
  classical
  unfold UNconv
  push_neg
  rfl

/-- Crown equivalence: global UN= failure is exactly inhabitation of the failure
object. -/
theorem not_UNconv_iff_nonempty_globalUNFailure (R : TRS sigma nu) :
    ¬ UNconv R ↔ Nonempty (GlobalUNFailure R) := by
  constructor
  · intro h
    rcases (not_UNconv_iff_exists_distinct_convertible_normalForms R).1 h with
      ⟨s, t, hs, ht, hconv, hne⟩
    exact ⟨{
      left := s
      right := t
      leftNormal := hs
      rightNormal := ht
      convertible := hconv
      distinct := hne }⟩
  · rintro ⟨f⟩
    exact f.not_UNconv

/-- Positive formulation of the same exact boundary. -/
theorem UNconv_iff_no_globalUNFailure (R : TRS sigma nu) :
    UNconv R ↔ ¬ Nonempty (GlobalUNFailure R) := by
  constructor
  · intro hun ⟨f⟩
    exact f.distinct (hun f.left f.right f.leftNormal f.rightNormal f.convertible)
  · intro hno
    by_contra hfail
    exact hno ((not_UNconv_iff_nonempty_globalUNFailure R).1 hfail)

/-- No global failure object can coexist with a UN= certificate. -/
theorem no_globalUNFailure_of_UNconv {R : TRS sigma nu} (hun : UNconv R) :
    ¬ Nonempty (GlobalUNFailure R) :=
  (UNconv_iff_no_globalUNFailure R).1 hun

/-! ## KO7 diagonal specialization -/

open OperatorKO7.Meta.UniqueNormalization.KO7Fence

/-- The concrete KO7 diagonal yields a global UN= failure object. Its left and
right endpoints are already terminal normal forms, not merely the immediate
branches of the peak. -/
def ko7DiagonalFailure : GlobalUNFailure ko7TRS where
  left := tVoid
  right := tIntVoid
  leftNormal := tVoid_normalForm
  rightNormal := tIntVoid_normalForm
  convertible := conv_void_intVoid
  distinct := by
    simp [tVoid, tIntVoid]

/-- The generic failure-object theorem reproduces the existing KO7 UN= failure
from the explicit diagonal object. -/
theorem ko7_not_UNconv_via_globalFailure : ¬ UNconv ko7TRS :=
  ko7DiagonalFailure.not_UNconv

/-- The local diagonal fork therefore inhabits the global failure type. -/
theorem ko7_globalFailure_nonempty : Nonempty (GlobalUNFailure ko7TRS) :=
  ⟨ko7DiagonalFailure⟩

/-- For KO7 the existing theorem and the failure-object existence statement are
exactly equivalent through the generic crown. -/
theorem ko7_not_UNconv_iff_failureObject :
    ¬ UNconv ko7TRS ↔ Nonempty (GlobalUNFailure ko7TRS) :=
  not_UNconv_iff_nonempty_globalUNFailure ko7TRS

#check @GlobalUNFailure.not_UNconv
#check @GlobalUNFailure.exists_data
#check @not_UNconv_iff_exists_distinct_convertible_normalForms
#check @not_UNconv_iff_nonempty_globalUNFailure
#check @UNconv_iff_no_globalUNFailure
#check @no_globalUNFailure_of_UNconv
#check ko7DiagonalFailure
#check ko7_not_UNconv_via_globalFailure
#check ko7_globalFailure_nonempty
#check ko7_not_UNconv_iff_failureObject

#print axioms GlobalUNFailure.not_UNconv
#print axioms GlobalUNFailure.exists_data
#print axioms not_UNconv_iff_exists_distinct_convertible_normalForms
#print axioms not_UNconv_iff_nonempty_globalUNFailure
#print axioms UNconv_iff_no_globalUNFailure
#print axioms no_globalUNFailure_of_UNconv
#print axioms ko7DiagonalFailure
#print axioms ko7_not_UNconv_via_globalFailure
#print axioms ko7_globalFailure_nonempty
#print axioms ko7_not_UNconv_iff_failureObject

end OperatorKO7.Meta.UniqueNormalization.GlobalFailure
