set_option autoImplicit false

/-!
This module defines a section-retraction pair and factorization through its collapse map. The
section equation makes collapse surjective onto PayloadCarrier, and factor_on_carrier determines
the factor map on that full carrier. Injectivity of collapse requires a separate hypothesis.























































-/

namespace OperatorKO7.RDRSSeedCollapse

/-- Data record whose requirements are the fields displayed below.






















-/
structure SeedCollapse (PayloadCarrier T : Type) where
  /-- Field requirements are given by the displayed type. -/
  carrier          : PayloadCarrier → T
  /-- Field requirements are given by the displayed type. -/
  collapse         : T → PayloadCarrier
  /-- Field requirements are given by the displayed type. -/
  collapse_carrier : ∀ b, collapse (carrier b) = b

/-- Data record whose requirements are the fields displayed below.

















-/
structure FactorsThroughSeedCollapse
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (obs : T → X) where
  /-- Field requirements are given by the displayed type. -/
  factor : PayloadCarrier → X
  /-- Field requirements are given by the displayed type. -/
  obs_eq : ∀ t, obs t = factor (SC.collapse t)

namespace FactorsThroughSeedCollapse

variable {PayloadCarrier T X : Type}
variable {SC : SeedCollapse PayloadCarrier T} {obs : T → X}

/-- The displayed proposition follows from the stated hypotheses.



















-/
theorem factor_on_carrier
    (F : FactorsThroughSeedCollapse SC obs) (b : PayloadCarrier) :
    F.factor b = obs (SC.carrier b) := by
  have h := F.obs_eq (SC.carrier b)
  rw [SC.collapse_carrier] at h
  exact h.symm

end FactorsThroughSeedCollapse

/-! Declarations for the section below. -/

/-- Definition with formal content given by the displayed type and body.










-/
def SeedCollapse.id (T : Type) : SeedCollapse T T where
  carrier          := fun b => b
  collapse         := fun t => t
  collapse_carrier := fun _ => rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem SeedCollapse_nonempty_diagonal (T : Type) :
    Nonempty (SeedCollapse T T) :=
  ⟨SeedCollapse.id T⟩

/-- Definition with formal content given by the displayed type and body.













-/
def FactorsThroughSeedCollapse.of_factor
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (obs : T → X)
    (factor : PayloadCarrier → X)
    (h : ∀ t, obs t = factor (SC.collapse t)) :
    FactorsThroughSeedCollapse SC obs :=
  { factor := factor
    obs_eq := h }

/-- The displayed proposition follows from the stated hypotheses.


-/
theorem FactorsThroughSeedCollapse_nonempty_of_factor
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (obs : T → X)
    (factor : PayloadCarrier → X)
    (h : ∀ t, obs t = factor (SC.collapse t)) :
    Nonempty (FactorsThroughSeedCollapse SC obs) :=
  ⟨FactorsThroughSeedCollapse.of_factor SC obs factor h⟩

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem FactorsThroughSeedCollapse_nonempty_const
    {PayloadCarrier T X : Type}
    (SC : SeedCollapse PayloadCarrier T) (x : X) :
    Nonempty (FactorsThroughSeedCollapse SC (fun _ : T => x)) :=
  ⟨{ factor := fun _ => x, obs_eq := fun _ => rfl }⟩

/-- Definition with formal content given by the displayed type and body.


-/
def rdrs_seed_collapse_anchor : String :=
  "OperatorKO7.RDRSSeedCollapse.SeedCollapse"

end OperatorKO7.RDRSSeedCollapse
