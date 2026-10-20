/-
OB-4.01 and OB-4.02: the data, laws and result factoring and the dependent coverage theorem.

The dependent-evidence layer stores, for each complementary row, an interpretation object and
states its laws and its row witness about that exact object. This module exposes that structure
under the audit names `MethodData`, `MethodLaws` and `MethodResult`, proves the factoring is
coherent, and restates the coverage theorem in factored form: every row selected by the dependent
certificate layer carries data whose laws and result are both about that same data.
-/
import OperatorKO7.Meta.Methods.OrientationClosure.DependentMethodEvidence

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodDataFactoring

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.Methods.OrientationClosure.NativeSemanticCoverage
open OperatorKO7.Methods.OrientationClosure.DependentMethodEvidence

/-- The data of a method row: the stored native interpretation object of its family. -/
abbrev MethodData (f : RDRSMethodFamily) : Type 1 := MissingNativeInterpretation f

/-- The laws of a method row: the package laws about the stored object. -/
abbrev MethodLaws {f : RDRSMethodFamily} (M : MethodData f) : Prop := NativeMethodLaws M

/-- The result of a method row: the row-specific witness about the stored object. -/
abbrev MethodResult {f : RDRSMethodFamily} (M : MethodData f) : Prop := NativeRowWitness M

/-- OB-4.01: the factoring is coherent. Laws and result refer to the same stored object, and the
package closure supplies the result from the laws. -/
theorem methodData_laws_result_factor {f : RDRSMethodFamily} (M : MethodData f) :
    MethodLaws M → MethodResult M :=
  fun _ => nativeRowWitness_closed M

/-- OB-4.01: every family with a stored interpretation object factors through the three audit
names, and the laws and result hold of that one object. -/
theorem methodData_factor_of_interpretation {f : RDRSMethodFamily}
    (i : MethodData f) : MethodLaws i ∧ MethodResult i :=
  ⟨nativeMethodLaws_closed i, nativeRowWitness_closed i⟩

/-- OB-4.02: the dependent coverage theorem in factored form. Every row selected by the dependent
certificate layer carries data whose laws and result are stated about that same data. -/
theorem methodData_rows_have_factor (f : RDRSMethodFamily) (hf : f ∈ dependentNativeRows) :
    ∃ M : MethodData f, MethodLaws M ∧ MethodResult M := by
  obtain ⟨c⟩ := dependentNativeRows_have_certificate f hf
  exact ⟨c.interpretation, c.laws, c.rowWitness⟩

/-- The factored layer covers exactly the sixty complementary rows. -/
theorem methodData_coverage_count : dependentNativeRows.length = 60 :=
  dependentNativeRows_count

/-- The factored row list is the same row identity list as the native-interpretation layer. -/
theorem methodData_rows_eq :
    dependentNativeRows = missingNativeInterpretationRows :=
  dependentNativeRows_eq_missingNativeInterpretationRows

end OperatorKO7.Methods.OrientationClosure.MethodDataFactoring
