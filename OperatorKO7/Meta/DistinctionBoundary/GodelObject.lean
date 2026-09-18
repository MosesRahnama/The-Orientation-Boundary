import OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
import OperatorKO7.Meta.LawvereYanofskySeparation
import OperatorKO7.Kernel
import OperatorKO7.Meta.Decision.ReflectiveDependencyPairs

set_option autoImplicit false

/-!
# The Godel object: external codes, schematic evaluation, Lawvere slots

Roadmap: ROADMAP-10, stages G1 through G6, plus the paper engine of
`Rahnama_The_Godel_Object`. This module fills the Lawvere absence record on a
*new* object. It does not edit `LawvereYanofskySeparation.lean`. It does not
inhabit `InternalToSignature` on Trace. It is not an incompleteness theorem.

Locks consumed: D-1 = A (Trace, external Code); D-2 = finite schematic
fragment with negative R5 at `delta`; D-3 = L-T; D-4 = both `diag_law` and
Lawvere `selfApplicationCorrect` on all codes.

Carrier adjacency: `C` is the kernel carrier `Trace`. Distinct R5 points are
`void` and `delta void`. Numerals embed by `natEncode`, so candidate C of the
roadmap has a compiled encoding even though the inhabitant is locked at A.

NameGate: no `goedel_first`, no `incompleteness`, no `feferman_completeness`.
Papers may cite this as the Godel *object* (slot-fill). They may not cite it
as Godel's theorem.

Relation: not applicable (carrier-level and code-level statements).
Closure: not applicable. Strategy: not applicable.
Trust: kernel only, Mathlib baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.Godel

open OperatorKO7
open OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
open OperatorKO7.LawvereYanofskySeparation

/-! ## Paper engine (any carrier, only `diag_law`) -/

/-- Self-application operator `S_D = diag ∘ quote`. -/
def selfap {C : Type*} (D : SelfEvaluationDiagonal C) : C → C :=
  fun x => D.diag (D.quote x)

/-- Paper representation: `ψ_D(x)(y) = eval (quote x) y`. -/
def represents {C : Type*} (D : SelfEvaluationDiagonal C) (f : C → C) : Prop :=
  ∃ x : C, ∀ y : C, D.eval (D.quote x) y = f y

/-- Fixed points from represented diagonals. Consumes only `diag_law` at the
witness, and totality of `eval` at `(quote x, x)`. -/
theorem fixed_point_from_represented_diagonal {C : Type*}
    (D : SelfEvaluationDiagonal C) (g : C → C) {x : C}
    (hx : ∀ y : C, D.eval (D.quote x) y = g (selfap D y)) :
    selfap D x = g (selfap D x) := by
  calc
    selfap D x = D.diag (D.quote x) := rfl
    _ = D.eval (D.quote x) x := D.diag_law x
    _ = g (selfap D x) := hx x

/-- Contrapositive: a fixed-point-free endomap is not represented after
composition with `S_D`. -/
theorem fixed_point_free_not_represented {C : Type*}
    (D : SelfEvaluationDiagonal C) (g : C → C)
    (hfp : ∀ v : C, g v ≠ v) :
    ¬ represents D (fun y => g (selfap D y)) := by
  rintro ⟨x, hx⟩
  exact hfp (selfap D x) (fixed_point_from_represented_diagonal D g hx).symm

/-- Successor obstruction: no self-evaluation structure on Trace represents
`delta ∘ S_D`. -/
theorem successor_obstruction (D : SelfEvaluationDiagonal Trace) :
    ¬ represents D (fun y => Trace.delta (selfap D y)) :=
  fixed_point_free_not_represented D Trace.delta delta_ne_self

/-- Self-exclusion: a class containing `S_D` and closed under left-`delta` is
not fully represented. -/
theorem self_exclusion (D : SelfEvaluationDiagonal Trace)
    (R : (Trace → Trace) → Prop)
    (hS : R (selfap D))
    (hcl : ∀ f, R f → R (fun x => Trace.delta (f x))) :
    ¬ (∀ f, R f → represents D f) := by
  intro hrep
  exact successor_obstruction D (hrep _ (hcl _ hS))

/-! ## G1/G2: external schematic codes on Trace -/

/-- Finite schematic fragment: projection, constants, composition. External to
the seven-constructor signature. -/
inductive SchematicCode : Type
  | proj
  | const (t : Trace)
  | compose (f g : SchematicCode)
  deriving DecidableEq, Repr

/-- Evaluation of a schematic code. Not the second projection. -/
def eval : SchematicCode → Trace → Trace
  | .proj, x => x
  | .const t, _ => t
  | .compose f g, x => eval f (eval g x)

/-- Const-quotation. -/
def quote (t : Trace) : SchematicCode :=
  .const t

/-- Decode a quotation; non-quotations collapse to `void`. -/
def unquote : SchematicCode → Trace
  | .const t => t
  | .proj => Trace.void
  | .compose _ _ => Trace.void

/-- Diagonal on codes: evaluate at `void`. -/
def diag (c : SchematicCode) : Trace :=
  eval c Trace.void

theorem eval_proj (x : Trace) : eval .proj x = x := rfl

theorem eval_const (t x : Trace) : eval (.const t) x = t := rfl

theorem eval_compose (f g : SchematicCode) (x : Trace) :
    eval (.compose f g) x = eval f (eval g x) := rfl

theorem unquote_quote (t : Trace) : unquote (quote t) = t := rfl

theorem quote_injective {a b : Trace} (h : quote a = quote b) : a = b := by
  cases h
  rfl

theorem quote_ne_of_ne {a b : Trace} (h : a ≠ b) : quote a ≠ quote b :=
  fun h' => h (quote_injective h')

/-- G1 R5: two distinct carrier points. -/
theorem carrier_r5 : Trace.void ≠ Trace.delta Trace.void :=
  (delta_ne_self Trace.void).symm

/-- G2 R5: distinct points have distinct codes. -/
theorem quote_separates_r5 :
    quote Trace.void ≠ quote (Trace.delta Trace.void) :=
  quote_ne_of_ne carrier_r5

/-- Depth of a schematic code. Quotation of any term has depth 1. -/
def codeDepth : SchematicCode → Nat
  | .proj => 0
  | .const _ => 1
  | .compose f g => codeDepth f + codeDepth g + 1

theorem quote_r5_depth_bound :
    codeDepth (quote Trace.void) = 1 ∧
      codeDepth (quote (Trace.delta Trace.void)) = 1 :=
  ⟨rfl, rfl⟩

/-- Numeral embedding. Candidate-C encoding, compiled on the locked carrier. -/
def natEncode : Nat → Trace
  | 0 => Trace.void
  | n + 1 => Trace.delta (natEncode n)

theorem natEncode_zero : natEncode 0 = Trace.void := rfl

theorem natEncode_succ (n : Nat) :
    natEncode (n + 1) = Trace.delta (natEncode n) := rfl

theorem natEncode_injective :
    ∀ {m n : Nat}, natEncode m = natEncode n → m = n := by
  intro m
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ _ => cases h
  | succ m ih =>
    intro n h
    cases n with
    | zero => cases h
    | succ n =>
      injection h with h'
      exact congrArg Nat.succ (ih h')

/-! ## G4: eval is not the degenerate second projection -/

theorem eval_not_second_projection :
    eval ≠ fun _ x => x := by
  intro h
  have hpt :=
    congrFun (congrFun h (.const Trace.void)) (Trace.delta Trace.void)
  exact carrier_r5 hpt

theorem const_void_represents_constant_void (x : Trace) :
    eval (.const Trace.void) x = Trace.void := rfl

theorem constant_void_ne_identity :
    (fun _ : Trace => Trace.void) ≠ (fun x : Trace => x) := by
  intro h
  have hpt := congrFun h (Trace.delta Trace.void)
  exact carrier_r5 hpt

/-! ## Dichotomy: every schematic evaluator is identity or constant -/

theorem eval_id_or_const (c : SchematicCode) :
    (∀ x, eval c x = x) ∨ (∃ t, ∀ x, eval c x = t) := by
  induction c with
  | proj => exact Or.inl fun _ => rfl
  | const t => exact Or.inr ⟨t, fun _ => rfl⟩
  | compose f g ihf ihg =>
    cases ihf with
    | inl hf =>
      cases ihg with
      | inl hg =>
        refine Or.inl fun x => ?_
        calc
          eval (.compose f g) x = eval f (eval g x) := rfl
          _ = eval g x := hf (eval g x)
          _ = x := hg x
      | inr ht =>
        obtain ⟨t, ht⟩ := ht
        refine Or.inr ⟨t, fun x => ?_⟩
        calc
          eval (.compose f g) x = eval f (eval g x) := rfl
          _ = eval f t := congrArg (eval f) (ht x)
          _ = t := hf t
    | inr hf =>
      obtain ⟨t, ht⟩ := hf
      exact Or.inr ⟨t, fun x => ht (eval g x)⟩

/-- Cleaner compose-constant case: if `f` is constant `t`, so is `compose f g`. -/
theorem eval_compose_of_const_left (g : SchematicCode) (t : Trace)
    (ht : ∀ x, eval (.const t) x = t) (x : Trace) :
    eval (.compose (.const t) g) x = t :=
  ht (eval g x)

theorem delta_not_identity : ¬ ∀ x, Trace.delta x = x :=
  fun h => delta_ne_self Trace.void (h Trace.void)

theorem delta_not_constant : ¬ ∃ t, ∀ x, Trace.delta x = t := by
  rintro ⟨t, ht⟩
  have h0 := ht Trace.void
  have h1 := ht (Trace.delta Trace.void)
  have h2 : Trace.delta Trace.void = Trace.delta (Trace.delta Trace.void) :=
    h0.trans h1.symm
  injection h2 with h3
  exact Trace.noConfusion h3

/-! ## G6 class `R`: code-represented schematic maps -/

/-- Official representability class: image of `eval`. -/
def CodeRepresented (f : Trace → Trace) : Prop :=
  ∃ c : SchematicCode, ∀ x, eval c x = f x

/-- Grammar of the class, constructor by constructor. -/
inductive Schematic : (Trace → Trace) → Prop
  | proj : Schematic (fun x => x)
  | const (t : Trace) : Schematic (fun _ => t)
  | compose {f g : Trace → Trace} :
      Schematic f → Schematic g → Schematic (fun x => f (g x))

theorem eval_schematic (c : SchematicCode) : Schematic (eval c) := by
  induction c with
  | proj => exact Schematic.proj
  | const t => exact Schematic.const t
  | compose f g ihf ihg =>
      exact Schematic.compose (f := eval f) (g := eval g) ihf ihg

theorem schematic_codeRepresented {f : Trace → Trace} (hf : Schematic f) :
    CodeRepresented f := by
  induction hf with
  | proj => exact ⟨.proj, fun _ => rfl⟩
  | const t => exact ⟨.const t, fun _ => rfl⟩
  | compose _ _ ihf ihg =>
    obtain ⟨cf, hcf⟩ := ihf
    obtain ⟨cg, hcg⟩ := ihg
    refine ⟨.compose cf cg, fun x => ?_⟩
    show eval cf (eval cg x) = _
    rw [hcg x]
    exact hcf _

theorem representability {f : Trace → Trace} (hf : Schematic f) :
    CodeRepresented f :=
  schematic_codeRepresented hf

theorem successor_not_codeRepresented : ¬ CodeRepresented Trace.delta := by
  rintro ⟨c, hc⟩
  cases eval_id_or_const c with
  | inl hid =>
    exact delta_ne_self Trace.void ((hc Trace.void).symm.trans (hid Trace.void))
  | inr ht =>
    obtain ⟨t, ht⟩ := ht
    exact delta_not_constant ⟨t, fun x => (hc x).symm.trans (ht x)⟩

theorem successor_not_schematic : ¬ Schematic Trace.delta :=
  fun h => successor_not_codeRepresented (schematic_codeRepresented h)

/-- Kill for "R empty or only identity": identity and a constant both inhabit
`R`, and they are distinct. -/
theorem schematic_class_not_only_identity :
    CodeRepresented (fun x => x) ∧
      CodeRepresented (fun _ => Trace.void) ∧
      (fun _ : Trace => Trace.void) ≠ (fun x => x) :=
  ⟨⟨.proj, fun _ => rfl⟩, ⟨.const Trace.void, fun _ => rfl⟩,
    constant_void_ne_identity⟩

/-- Compiled cost of the smaller-class escape: every code-represented map
is the identity or a constant. -/
theorem codeRepresented_collapses_to_id_or_const {f : Trace → Trace}
    (h : CodeRepresented f) :
    (∀ x, f x = x) ∨ (∃ t, ∀ x, f x = t) := by
  obtain ⟨c, hc⟩ := h
  cases eval_id_or_const c with
  | inl hid => exact Or.inl fun x => (hc x).symm.trans (hid x)
  | inr ht =>
    obtain ⟨t, ht⟩ := ht
    exact Or.inr ⟨t, fun x => (hc x).symm.trans (ht x)⟩

/-- Sharper kill this object fails: a represented map that depends on its
argument and is not the identity. Identity occupies one disjunct;
constants occupy the other. -/
theorem schematic_fails_sharp_kill :
    ¬ ∃ f : Trace → Trace,
        CodeRepresented f ∧ (∃ x y, f x ≠ f y) ∧ (∃ x, f x ≠ x) := by
  rintro ⟨f, hf, ⟨x, y, hxy⟩, ⟨z, hz⟩⟩
  cases codeRepresented_collapses_to_id_or_const hf with
  | inl hid => exact hz (hid z)
  | inr ht =>
    obtain ⟨t, ht⟩ := ht
    exact hxy ((ht x).trans (ht y).symm)

/-! ## G3: substitute (freeze update) -/

/-- Freeze update: the substituted value ignores the live argument. -/
def update (x _y : Trace) : Trace := x

/-- Substitute the quotation of `x` under `c`. -/
def substitute (c : SchematicCode) (x : Trace) : SchematicCode :=
  .compose c (quote x)

theorem subst_eval (c : SchematicCode) (x y : Trace) :
    eval (substitute c x) y = eval c (update x y) :=
  rfl

/-- G3 R5: substitute a constant at a concrete point. -/
theorem subst_eval_r5 :
    eval (substitute (.const Trace.void) (Trace.delta Trace.void))
      (Trace.merge Trace.void Trace.void) = Trace.void :=
  rfl

/-- Freeze substitution on `proj` writes the quoted value, not the live
argument. This is the hole-substitution failure object: const-quote has
no holes, so G3 cannot track a live update. -/
theorem substitute_proj_freezes_live_argument (x y : Trace) :
    eval (substitute .proj x) y = x :=
  rfl

theorem live_proj (y : Trace) : eval .proj y = y := rfl

/-- Duck: freeze versus live is the same peak as stale quotation. -/
theorem freeze_and_live_disagree {x y : Trace} (h : x ≠ y) :
    eval (substitute .proj x) y ≠ eval .proj y := by
  simpa [substitute_proj_freezes_live_argument, live_proj] using h

/-- No live-hole update agrees with freeze substitution on `proj`. -/
theorem live_update_ne_freeze_update {x y : Trace} (h : x ≠ y) :
    update x y ≠ y :=
  h

/-! ## G5: D2 inhabitant, both equations, Lawvere export -/

def schematicSelfEvaluation : SelfEvaluationDiagonal Trace where
  Code := SchematicCode
  quote := quote
  eval := eval
  diag := diag
  diag_law := fun _ => rfl

/-- RESOLVED-NEGATIVELY for "self-application is not identity": const-quote
forces `S_D = id`. Failure object, not a miss. -/
theorem const_quote_forces_identity_selfap (x : Trace) :
    selfap schematicSelfEvaluation x = x := rfl

theorem diag_quote_eq_carrier (x : Trace) :
    schematicSelfEvaluation.diag (schematicSelfEvaluation.quote x) = x := rfl

/-- Quote-representation sees only constants, because `eval (quote x)` is
constantly `x`. -/
theorem quote_represented_are_constants {f : Trace → Trace}
    (h : represents schematicSelfEvaluation f) :
    ∃ t, ∀ y, f y = t := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, fun y => (hx y).symm⟩

/-- Smaller-class escape, named: the object represents `id` by a *code*
(`proj`), not by a quotation, and omits `delta ∘ S_D`. -/
theorem schematic_takes_smaller_class_escape :
    CodeRepresented (selfap schematicSelfEvaluation) ∧
      ¬ CodeRepresented (fun y => Trace.delta (selfap schematicSelfEvaluation y)) ∧
      ¬ represents schematicSelfEvaluation (selfap schematicSelfEvaluation) :=
  ⟨⟨.proj, fun _ => rfl⟩, successor_not_codeRepresented, by
    intro h
    obtain ⟨t, ht⟩ := quote_represented_are_constants h
    exact carrier_r5
      ((ht Trace.void).trans (ht (Trace.delta Trace.void)).symm)⟩

theorem schematic_not_internal :
    ¬ Nonempty (InternalToSignature schematicSelfEvaluation) :=
  no_internal_selfEvaluationDiagonal schematicSelfEvaluation

theorem trivial_cannot_represent_constant_void :
    ¬ ∃ c : trivialSelfEvaluationDiagonal.Code,
        ∀ x, trivialSelfEvaluationDiagonal.eval c x = Trace.void := by
  rintro ⟨c, hc⟩
  exact carrier_r5 (hc (Trace.delta Trace.void)).symm

/-- Lawvere code object, route L-T. -/
def toCodeObject : LawvereCodeObject where
  Code := SchematicCode
  quote := quote

/-- Unquote on the second code argument, then evaluate. -/
def lawvereEvaluate (c d : SchematicCode) : Trace :=
  eval c (unquote d)

theorem lawvereEvaluate_self (c : SchematicCode) :
    lawvereEvaluate c c = eval c (unquote c) := rfl

theorem selfApplicationCorrect_on_all_codes (c : SchematicCode) :
    eval c Trace.void = eval c (unquote c) := by
  cases c with
  | proj => rfl
  | const t => rfl
  | compose f g => rfl

def toEvalMap : LawvereEvaluationMap where
  Code := SchematicCode
  Value := Trace
  represent := fun c => eval c Trace.void
  evaluate := lawvereEvaluate
  selfApplicationCode := id
  selfApplicationCorrect := fun c => selfApplicationCorrect_on_all_codes c

/-- RESOLVED-NEGATIVELY for "diagonal is not identity on codes": the Lawvere
self-application combinator is `id`. -/
theorem selfApplicationCode_is_identity :
    toEvalMap.selfApplicationCode = id := rfl

def toFixedPointFree : FixedPointFreeEndomap where
  Value := Trace
  endomap := Trace.delta
  isFixedPointFree := delta_ne_self

def toSchema : LawvereYanofskySchema where
  codeObject := toCodeObject
  evaluationMap := toEvalMap
  fixedPointFreeEndomap := toFixedPointFree
  codeTypesAgree := rfl
  valueTypesAgree := rfl

/-! ## Package inhabitant (G1–G5 data; G6 is a theorem about it) -/

structure GodelPackage where
  diagonal : SelfEvaluationDiagonal Trace
  substitute : diagonal.Code → Trace → diagonal.Code
  update : Trace → Trace → Trace
  subst_eval :
    ∀ (c : diagonal.Code) (x y : Trace),
      diagonal.eval (substitute c x) y = diagonal.eval c (update x y)

def schematicPackage : GodelPackage where
  diagonal := schematicSelfEvaluation
  substitute := substitute
  update := update
  subst_eval := subst_eval

/-! ## Escape 1: partiality. The total theorem is the `some` case. -/

structure PartialSelfEvaluation (C : Type*) where
  Code : Type*
  quote : C → Code
  eval? : Code → C → Option C
  diag? : Code → Option C
  diag_law : ∀ x : C, diag? (quote x) = eval? (quote x) x

def selfap? {C : Type*} (D : PartialSelfEvaluation C) (x : C) : Option C :=
  D.diag? (D.quote x)

/-- Kleene-shaped recovery: when the represented composite is defined at the
witness, the value is a fixed point of `g`. -/
theorem partial_fixed_point_when_defined {C : Type*}
    (D : PartialSelfEvaluation C) (g : C → C) {x z : C}
    (hrep : ∀ y, D.eval? (D.quote x) y = (selfap? D y).map g)
    (hdef : selfap? D x = some z) :
    g z = z := by
  have hcalc :
      some z = some (g z) := by
    calc
      some z = selfap? D x := hdef.symm
      _ = D.diag? (D.quote x) := rfl
      _ = D.eval? (D.quote x) x := D.diag_law x
      _ = (selfap? D x).map g := hrep x
      _ = (some z).map g := by rw [hdef]
      _ = some (g z) := rfl
  injection hcalc with hzg
  exact hzg.symm

def toPartial {C : Type*} (D : SelfEvaluationDiagonal C) :
    PartialSelfEvaluation C where
  Code := D.Code
  quote := D.quote
  eval? c x := some (D.eval c x)
  diag? c := some (D.diag c)
  diag_law := fun x => congrArg some (D.diag_law x)

theorem total_selfap_is_defined_partial {C : Type*}
    (D : SelfEvaluationDiagonal C) (x : C) :
    selfap? (toPartial D) x = some (selfap D x) := rfl

/-- Totality boundary: the paper theorem is the partial theorem at `some`. -/
theorem partial_specializes_to_total {C : Type*}
    (D : SelfEvaluationDiagonal C) (g : C → C) {x : C}
    (hx : ∀ y, D.eval (D.quote x) y = g (selfap D y)) :
    (∀ y, (toPartial D).eval? ((toPartial D).quote x) y =
      (selfap? (toPartial D) y).map g) ∧
      selfap? (toPartial D) x = some (selfap D x) ∧
      g (selfap D x) = selfap D x := by
  refine ⟨?_, total_selfap_is_defined_partial D x, ?_⟩
  · intro y
    change some (D.eval (D.quote x) y) = Option.map g (some (selfap D y))
    rw [hx y]
    rfl
  · exact (fixed_point_from_represented_diagonal D g hx).symm

/-- Failure object: evaluation nowhere defined yields no diagonal value. -/
def nowherePartial : PartialSelfEvaluation Trace where
  Code := SchematicCode
  quote := quote
  eval? _ _ := none
  diag? _ := none
  diag_law := fun _ => rfl

theorem nowhere_selfap_undefined (x : Trace) :
    selfap? nowherePartial x = none := rfl

/-! ## Escape 2: separate value type. Obstruction relocates to `V`. -/

structure SeparateValueDiagonal (C : Type*) (V : Type*) where
  Code : Type*
  quote : C → Code
  eval : Code → C → V

def valueSelfap {C V : Type*} (D : SeparateValueDiagonal C V) : C → V :=
  fun x => D.eval (D.quote x) x

def unitValued : SeparateValueDiagonal Trace Unit where
  Code := SchematicCode
  quote := quote
  eval := fun _ _ => ()

theorem unit_has_no_fixed_point_free_endomap (h : Unit → Unit) :
    ∃ v, h v = v :=
  ⟨(), rfl⟩

/-- No retraction restores a carrier self-application from the unit-valued
evaluator: `valueSelfap` is constantly `()`. -/
theorem unit_valued_has_no_retraction :
    ¬ ∃ decode : Unit → Trace, ∀ t, decode (valueSelfap unitValued t) = t := by
  rintro ⟨decode, h⟩
  exact carrier_r5 ((h Trace.void).symm.trans (h (Trace.delta Trace.void)))

/-! ## Every schematic map has a fixed point (total small-class recursion) -/

theorem schematic_has_fixed_point (c : SchematicCode) :
    ∃ G : Trace, eval c G = G := by
  cases eval_id_or_const c with
  | inl hid => exact ⟨Trace.void, hid Trace.void⟩
  | inr ht =>
    obtain ⟨t, ht⟩ := ht
    exact ⟨t, ht t⟩

end OperatorKO7.Meta.DistinctionBoundary.Godel
