/-!
This module packages implications with typed side conditions. Composition chains implications,
the True constructor embeds an available conclusion, and associativity concerns the stored
discharge functions.







-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalConditionalBound

/-- Data record whose requirements are the fields displayed below.
-/
structure ConditionalBound where
  SideCondition : Prop
  Conclusion : Prop
  discharge : SideCondition → Conclusion

namespace ConditionalBound

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem holds (C : ConditionalBound) (h : C.SideCondition) : C.Conclusion :=
  C.discharge h

/-- Definition with formal content given by the displayed type and body.
-/
def comp (C₁ C₂ : ConditionalBound) (link : C₁.Conclusion → C₂.SideCondition) :
    ConditionalBound where
  SideCondition := C₁.SideCondition
  Conclusion := C₂.Conclusion
  discharge := fun s => C₂.discharge (link (C₁.discharge s))

/-- The displayed proposition follows from the stated hypotheses. -/
theorem comp_holds (C₁ C₂ : ConditionalBound)
    (link : C₁.Conclusion → C₂.SideCondition) (h : C₁.SideCondition) :
    (C₁.comp C₂ link).Conclusion :=
  (C₁.comp C₂ link).holds h

/-- Definition with formal content given by the displayed type and body.
-/
def ofUnconditional {P : Prop} (h : P) : ConditionalBound where
  SideCondition := True
  Conclusion := P
  discharge := fun _ => h

/-- The displayed proposition follows from the stated hypotheses. -/
theorem ofUnconditional_holds {P : Prop} (h : P) : (ofUnconditional h).Conclusion :=
  (ofUnconditional h).holds trivial

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem comp_assoc_discharge
    (C₁ C₂ C₃ : ConditionalBound)
    (l₁₂ : C₁.Conclusion → C₂.SideCondition)
    (l₂₃ : C₂.Conclusion → C₃.SideCondition)
    (h : C₁.SideCondition) :
    C₃.discharge (l₂₃ (C₂.discharge (l₁₂ (C₁.discharge h))))
      = ((C₁.comp C₂ l₁₂).comp C₃ l₂₃).discharge h :=
  rfl

end ConditionalBound

/-- Definition with formal content given by the displayed type and body.
-/
def exampleConditional : ConditionalBound where
  SideCondition := True
  Conclusion := (0 : Nat) ≤ 1
  discharge := fun _ => Nat.zero_le 1

/-- Definition with formal content given by the displayed type and body. -/
def universal_conditional_bound_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalConditionalBound.ConditionalBound.comp"

end OperatorKO7.Meta.BoundaryOperator.UniversalConditionalBound
