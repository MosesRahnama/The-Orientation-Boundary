import OperatorKO7.Meta.UUET.Quantum.FiniteHilbert

set_option autoImplicit false

/-!
# Pure two-qubit amplitudes

Relation: equality and product factorization of `2 x 2` complex amplitude tables.
Closure: exact determinant criterion over the complex field.
Trust: kernel-checked finite case analysis and field algebra.
Scope: pure two-qubit amplitudes only; mixed-state separability is not claimed.
-/

namespace OperatorKO7.Meta.UUET.Quantum

/-- Pure two-qubit amplitude table. -/
abbrev TwoQubitAmplitude := Fin 2 -> Fin 2 -> ℂ

/-- The `2 x 2` amplitude determinant. -/
def amplitudeDet (A : TwoQubitAmplitude) : ℂ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- Product-state factorization of a two-qubit amplitude. -/
def ProductAmplitude (A : TwoQubitAmplitude) : Prop :=
  Exists fun u : Fin 2 -> ℂ => Exists fun v : Fin 2 -> ℂ =>
    forall i j, A i j = u i * v j

/-- Every product amplitude has zero determinant. -/
theorem productAmplitude_det_zero {A : TwoQubitAmplitude}
    (hA : ProductAmplitude A) : amplitudeDet A = 0 := by
  rcases hA with ⟨u, v, h⟩
  simp only [amplitudeDet, h]
  ring

/-- Exact two-qubit criterion: product factorization iff determinant zero. -/
theorem productAmplitude_iff_det_zero (A : TwoQubitAmplitude) :
    ProductAmplitude A <-> amplitudeDet A = 0 := by
  constructor
  · exact productAmplitude_det_zero
  · intro hdet
    by_cases h00 : A 0 0 = 0
    · by_cases h01 : A 0 1 = 0
      · refine ⟨![0, 1], ![A 1 0, A 1 1], ?_⟩
        intro i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01]
      · have h10 : A 1 0 = 0 := by
          have hprod : A 0 1 * A 1 0 = 0 := by
            simpa [amplitudeDet, h00] using hdet
          exact (mul_eq_zero.mp hprod).resolve_left h01
        refine ⟨![1, A 1 1 / A 0 1], ![0, A 0 1], ?_⟩
        intro i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01, h10]
    · refine ⟨![1, A 1 0 / A 0 0], ![A 0 0, A 0 1], ?_⟩
      intro i j
      fin_cases i <;> fin_cases j
      · simp
      · simp
      · simp [h00]
      · have hmul : A 0 0 * A 1 1 = A 0 1 * A 1 0 :=
          sub_eq_zero.mp hdet
        calc
          A 1 1 = (A 1 0 * A 0 1) / A 0 0 := by
            apply (eq_div_iff h00).2
            simpa [mul_comm] using hmul
          _ = (A 1 0 / A 0 0) * A 0 1 := by
            field_simp [h00]

/-- Positive product fixture `|0> tensor |0>`. -/
def productZeroZero : TwoQubitAmplitude :=
  fun i j => if i = 0 /\ j = 0 then 1 else 0

theorem productZeroZero_is_product : ProductAmplitude productZeroZero := by
  refine ⟨![1, 0], ![1, 0], ?_⟩
  have h :
      productZeroZero =
        fun i j => (![1, 0] : Fin 2 → ℂ) i * (![1, 0] : Fin 2 → ℂ) j := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [productZeroZero]
  intro i j
  exact congrFun (congrFun h i) j

/-! Imported NameGate and TypeGate. -/
#check @sub_eq_zero.mp
#check @eq_div_iff
#check @mul_eq_zero.mp
#check @ProductAmplitude

#check @productAmplitude_det_zero
#print axioms productAmplitude_det_zero
#check @productAmplitude_iff_det_zero
#print axioms productAmplitude_iff_det_zero
#check @productZeroZero_is_product
#print axioms productZeroZero_is_product

end OperatorKO7.Meta.UUET.Quantum
