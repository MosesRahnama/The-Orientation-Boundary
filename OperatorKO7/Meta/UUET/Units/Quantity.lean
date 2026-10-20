import Mathlib

set_option autoImplicit false

/-!
# Dimension-indexed UUET quantities

Relation: equality and order on exact rational quantities indexed by dimension.
Closure: pointwise dimension algebra and same-dimension quantity arithmetic.
Trust: kernel-only finite algebra, with no external or runtime trust.
Scope: typed accounting only. Distinct dimensions require an explicit conversion
morphism before their values can interact.
-/

namespace OperatorKO7.Meta.UUET.Units

/-- Primitive dimensions used by the terminal UUET spine. -/
inductive BaseDimension
  | dimensionless
  | informationBit
  | energy
  | time
  | length
  | temperature
  | action
  | probability
  | count
  | assumption
  | oracleCall
  | comparison
  deriving DecidableEq, Fintype, Repr

/-- A dimension is an integer exponent for every primitive dimension. -/
structure Dimension where
  exponent : BaseDimension -> Int
  deriving DecidableEq

namespace Dimension

/-- Dimensionless quantity index. -/
def one : Dimension := ⟨fun _ => 0⟩

/-- A single primitive dimension. -/
def basis (b : BaseDimension) : Dimension :=
  ⟨fun b' => if b' = b then 1 else 0⟩

/-- Product of dimensions adds their exponents. -/
def mul (d e : Dimension) : Dimension :=
  ⟨fun b => d.exponent b + e.exponent b⟩

/-- Quotient of dimensions subtracts their exponents. -/
def div (d e : Dimension) : Dimension :=
  ⟨fun b => d.exponent b - e.exponent b⟩

theorem mul_exponent (d e : Dimension) (b : BaseDimension) :
    (mul d e).exponent b = d.exponent b + e.exponent b := rfl

theorem div_exponent (d e : Dimension) (b : BaseDimension) :
    (div d e).exponent b = d.exponent b - e.exponent b := rfl

end Dimension

def dimensionless : Dimension := Dimension.one
def informationDimension : Dimension := Dimension.basis .informationBit
def energyDimension : Dimension := Dimension.basis .energy
def timeDimension : Dimension := Dimension.basis .time
def actionDimension : Dimension := Dimension.basis .action
def countDimension : Dimension := Dimension.basis .count

/-- An exact rational quantity whose dimension is part of its type. -/
structure Quantity (d : Dimension) where
  value : Rat
  deriving DecidableEq, Repr

namespace Quantity

def zero (d : Dimension) : Quantity d := ⟨0⟩

/-- Addition is available only at one fixed dimension. -/
def add {d : Dimension} (x y : Quantity d) : Quantity d :=
  ⟨x.value + y.value⟩

def neg {d : Dimension} (x : Quantity d) : Quantity d :=
  ⟨-x.value⟩

def sub {d : Dimension} (x y : Quantity d) : Quantity d :=
  ⟨x.value - y.value⟩

def mul {d e : Dimension} (x : Quantity d) (y : Quantity e) :
    Quantity (Dimension.mul d e) :=
  ⟨x.value * y.value⟩

def div {d e : Dimension} (x : Quantity d) (y : Quantity e) :
    Quantity (Dimension.div d e) :=
  ⟨x.value / y.value⟩

def LE {d : Dimension} (x y : Quantity d) : Prop := x.value <= y.value

theorem add_value {d : Dimension} (x y : Quantity d) :
    (add x y).value = x.value + y.value := rfl

theorem add_assoc {d : Dimension} (x y z : Quantity d) :
    add (add x y) z = add x (add y z) := by
  cases x
  cases y
  cases z
  simp [add, _root_.add_assoc]

theorem le_refl {d : Dimension} (x : Quantity d) : LE x x := by
  exact _root_.le_refl _

theorem le_trans {d : Dimension} {x y z : Quantity d}
    (hxy : LE x y) (hyz : LE y z) : LE x z :=
  _root_.le_trans hxy hyz

end Quantity

/-- Existential packaging used only at dynamic boundaries. -/
structure SomeQuantity where
  dimension : Dimension
  quantity : Quantity dimension

/-- Dynamic addition either returns a same-dimension sum or a typed refusal. -/
inductive AdditionVerdict
  | admitted (result : SomeQuantity)
  | refused

def checkedAdd (x y : SomeQuantity) : AdditionVerdict :=
  if h : x.dimension = y.dimension then
    let yAtX : Quantity x.dimension := h.symm ▸ y.quantity
    .admitted ⟨x.dimension, Quantity.add x.quantity yAtX⟩
  else
    .refused

theorem energyDimension_ne_timeDimension :
    Not (energyDimension = timeDimension) := by
  intro h
  have hEnergy := congrArg (fun d => d.exponent .energy) h
  simp [energyDimension, timeDimension, Dimension.basis] at hEnergy

def energyFixture : SomeQuantity := ⟨energyDimension, ⟨2⟩⟩
def timeFixture : SomeQuantity := ⟨timeDimension, ⟨3⟩⟩

/-- Positive fixture: quantities of one dimension add normally. -/
theorem same_dimension_addition_fixture :
    Quantity.add (d := energyDimension) ⟨2⟩ ⟨3⟩ = ⟨5⟩ := by
  norm_num [Quantity.add]

/-- Negative fixture: energy and time are refused at the dynamic boundary. -/
theorem mixed_dimension_addition_refused :
    checkedAdd energyFixture timeFixture = .refused := by
  simp [checkedAdd, energyFixture, timeFixture, energyDimension_ne_timeDimension]

/-! Imported NameGate and TypeGate. -/
#check @congrArg
#check @Int.add
#check @Quantity.add
#check @checkedAdd
#check @Dimension.mul_exponent
#check @Dimension.div_exponent
#check @Quantity.add_value
#check @Quantity.add_assoc
#check @Quantity.le_refl
#check @Quantity.le_trans
#check @energyDimension_ne_timeDimension
#check @same_dimension_addition_fixture
#check @mixed_dimension_addition_refused

#print axioms Dimension.mul_exponent
#print axioms Dimension.div_exponent
#print axioms Quantity.add_value
#print axioms Quantity.add_assoc
#print axioms Quantity.le_refl
#print axioms Quantity.le_trans
#print axioms energyDimension_ne_timeDimension
#print axioms same_dimension_addition_fixture
#print axioms mixed_dimension_addition_refused

end OperatorKO7.Meta.UUET.Units
