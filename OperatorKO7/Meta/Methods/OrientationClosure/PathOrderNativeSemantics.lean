import OperatorKO7.Meta.Methods.PathOrderRows
import Mathlib.Data.Prod.Lex

/-!
# Native path-order semantics for ORI-1

The KBO-family carriers below compute their comparison relation from the
method's weights, precedence, status, AC theory, ordinal weights, applicative
encoding, or polynomial weight functions. There is no field containing an
unrelated comparator. Every comparison carries the variable condition that
blocks the duplicating schema rule.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.PathOrderNativeSemantics

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.Methods.PathOrderRows

/-! ## Shared syntax operations -/

/-- Root symbol when a schema term has a function-symbol root. -/
def methodRoot : STerm → Option MethodSymbol
  | .var _ => none
  | .base => some .base
  | .succ _ => some .succ
  | .wrap _ _ => some .wrap
  | .recur _ _ _ => some .recur

/-- Standard variable condition. -/
def NativeVariableCondition (x y : STerm) : Prop :=
  ∀ v : SchemaVar, countVar v y ≤ countVar v x

/-- A substitution on the three-variable schema. -/
abbrev SchemaSubstitution := SchemaVar → STerm

/-- Simultaneous schema substitution. -/
@[simp] def schemaSubstitute (σ : SchemaSubstitution) : STerm → STerm
  | .var v => σ v
  | .base => .base
  | .succ t => .succ (schemaSubstitute σ t)
  | .wrap x y => .wrap (schemaSubstitute σ x) (schemaSubstitute σ y)
  | .recur b s n =>
      .recur (schemaSubstitute σ b) (schemaSubstitute σ s) (schemaSubstitute σ n)

/-- Variable counts after simultaneous substitution. -/
theorem countVar_schemaSubstitute (σ : SchemaSubstitution) (v : SchemaVar)
    (t : STerm) :
    countVar v (schemaSubstitute σ t) =
      countVar SchemaVar.b t * countVar v (σ SchemaVar.b) +
      countVar SchemaVar.s t * countVar v (σ SchemaVar.s) +
      countVar SchemaVar.n t * countVar v (σ SchemaVar.n) := by
  induction t with
  | var w =>
      cases w <;> simp [schemaSubstitute, countVar]
  | base => simp [schemaSubstitute, countVar]
  | succ t ih => simpa [schemaSubstitute, countVar] using ih
  | wrap x y ihx ihy =>
      simp [schemaSubstitute, countVar, ihx, ihy]
      ring
  | recur b s n ihb ihs ihn =>
      simp [schemaSubstitute, countVar, ihb, ihs, ihn]
      ring

/-- The KBO variable condition is closed under simultaneous substitution. -/
theorem nativeVariableCondition_substitute {x y : STerm}
    (h : NativeVariableCondition x y) (σ : SchemaSubstitution) :
    NativeVariableCondition (schemaSubstitute σ x) (schemaSubstitute σ y) := by
  intro v
  rw [countVar_schemaSubstitute, countVar_schemaSubstitute]
  have hb := Nat.mul_le_mul_right (countVar v (σ SchemaVar.b)) (h SchemaVar.b)
  have hs := Nat.mul_le_mul_right (countVar v (σ SchemaVar.s)) (h SchemaVar.s)
  have hn := Nat.mul_le_mul_right (countVar v (σ SchemaVar.n)) (h SchemaVar.n)
  omega

/-- One-hole schema contexts. -/
inductive SchemaContext where
  | hole
  | succ : SchemaContext → SchemaContext
  | wrapLeft : SchemaContext → STerm → SchemaContext
  | wrapRight : STerm → SchemaContext → SchemaContext
  | recurBase : SchemaContext → STerm → STerm → SchemaContext
  | recurStep : STerm → SchemaContext → STerm → SchemaContext
  | recurCounter : STerm → STerm → SchemaContext → SchemaContext

namespace SchemaContext

/-- Plug a term into the unique context hole. -/
@[simp] def plug : SchemaContext → STerm → STerm
  | .hole, t => t
  | .succ C, t => .succ (plug C t)
  | .wrapLeft C y, t => .wrap (plug C t) y
  | .wrapRight x C, t => .wrap x (plug C t)
  | .recurBase C s n, t => .recur (plug C t) s n
  | .recurStep b C n, t => .recur b (plug C t) n
  | .recurCounter b s C, t => .recur b s (plug C t)

end SchemaContext

/-- The variable condition is preserved when the same context is added to both
sides. -/
theorem nativeVariableCondition_context (C : SchemaContext) {x y : STerm}
    (h : NativeVariableCondition x y) :
    NativeVariableCondition (C.plug x) (C.plug y) := by
  induction C with
  | hole => exact h
  | succ C ih =>
      intro v
      simpa [SchemaContext.plug, countVar] using ih v
  | wrapLeft C z ih =>
      intro v
      have hv := ih v
      simp [SchemaContext.plug, countVar]
      omega
  | wrapRight z C ih =>
      intro v
      have hv := ih v
      simp [SchemaContext.plug, countVar]
      omega
  | recurBase C s n ih =>
      intro v
      have hv := ih v
      simp [SchemaContext.plug, countVar]
      omega
  | recurStep b C n ih =>
      intro v
      have hv := ih v
      simp [SchemaContext.plug, countVar]
      omega
  | recurCounter b s C ih =>
      intro v
      have hv := ih v
      simp [SchemaContext.plug, countVar]
      omega

/-- Least substitution- and context-compatible closure of a native base
comparison. -/
inductive CompatibleClosure (base : STerm → STerm → Prop) : STerm → STerm → Prop
  | baseStep {x y : STerm} : base x y → CompatibleClosure base x y
  | context {x y : STerm} (C : SchemaContext) :
      CompatibleClosure base x y → CompatibleClosure base (C.plug x) (C.plug y)
  | substitute {x y : STerm} (σ : SchemaSubstitution) :
      CompatibleClosure base x y →
        CompatibleClosure base (schemaSubstitute σ x) (schemaSubstitute σ y)

/-- Any compatible closure whose base relation satisfies the variable
condition still satisfies it after arbitrary contexts and substitutions. -/
theorem CompatibleClosure.variableCondition
    {base : STerm → STerm → Prop}
    (hbase : ∀ {x y}, base x y → NativeVariableCondition x y)
    {x y : STerm} (h : CompatibleClosure base x y) : NativeVariableCondition x y := by
  induction h with
  | baseStep hxy => exact hbase hxy
  | context C hxy ih => exact nativeVariableCondition_context C ih
  | substitute σ hxy ih => exact nativeVariableCondition_substitute ih σ

/-! ## KBO with argument status -/

/-- Native KBO data. All fields enter either the weight, precedence or status
clauses of `NativeKBOGt`. -/
structure NativeKBOData where
  variableWeight : Nat
  variableWeight_pos : 0 < variableWeight
  symbolWeight : MethodSymbol → Nat
  constantWeight_ge_variable : variableWeight ≤ symbolWeight .base
  precedenceRank : MethodSymbol → Nat
  precedenceRank_injective : Function.Injective precedenceRank
  status : MethodSymbol → ArgStatus
  zeroWeightOnlySucc : ∀ f, symbolWeight f = 0 → f = .succ
  zeroWeightSuccMaximal : symbolWeight .succ = 0 →
    ∀ f, f ≠ .succ → precedenceRank f < precedenceRank .succ

/-- Additive KBO weight computed from the method object. -/
@[simp] def nativeKBOWeight (K : NativeKBOData) : STerm → Nat
  | .var _ => K.variableWeight
  | .base => K.symbolWeight .base
  | .succ t => K.symbolWeight .succ + nativeKBOWeight K t
  | .wrap x y => K.symbolWeight .wrap + nativeKBOWeight K x + nativeKBOWeight K y
  | .recur b s n =>
      K.symbolWeight .recur + nativeKBOWeight K b + nativeKBOWeight K s + nativeKBOWeight K n

/-- Root precedence key; variables sit below function-symbol roots. -/
def nativeKBORootRank (K : NativeKBOData) : STerm → Nat
  | .var _ => 0
  | t => match methodRoot t with
    | none => 0
    | some f => K.precedenceRank f + 1

/-- Native status-aware KBO comparison clauses. Lexicographic and multiset
branches are separate constructors and are selected by `K.status`. -/
inductive NativeKBOGt (K : NativeKBOData) : STerm → STerm → Prop
  | weight {x y : STerm}
      (vc : NativeVariableCondition x y)
      (hweight : nativeKBOWeight K y < nativeKBOWeight K x) : NativeKBOGt K x y
  | precedence {x y : STerm}
      (vc : NativeVariableCondition x y)
      (hweight : nativeKBOWeight K x = nativeKBOWeight K y)
      (hprec : nativeKBORootRank K y < nativeKBORootRank K x) : NativeKBOGt K x y
  | succLex {x y : STerm}
      (hstatus : K.status .succ = .lex)
      (vc : NativeVariableCondition (.succ x) (.succ y))
      (hweight : nativeKBOWeight K (.succ x) = nativeKBOWeight K (.succ y))
      (harg : NativeKBOGt K x y) : NativeKBOGt K (.succ x) (.succ y)
  | wrapLexLeft {x₁ x₂ y₁ y₂ : STerm}
      (hstatus : K.status .wrap = .lex)
      (vc : NativeVariableCondition (.wrap x₁ x₂) (.wrap y₁ y₂))
      (hweight : nativeKBOWeight K (.wrap x₁ x₂) = nativeKBOWeight K (.wrap y₁ y₂))
      (harg : NativeKBOGt K x₁ y₁) : NativeKBOGt K (.wrap x₁ x₂) (.wrap y₁ y₂)
  | wrapLexRight {x₁ x₂ y₂ : STerm}
      (hstatus : K.status .wrap = .lex)
      (vc : NativeVariableCondition (.wrap x₁ x₂) (.wrap x₁ y₂))
      (hweight : nativeKBOWeight K (.wrap x₁ x₂) = nativeKBOWeight K (.wrap x₁ y₂))
      (harg : NativeKBOGt K x₂ y₂) : NativeKBOGt K (.wrap x₁ x₂) (.wrap x₁ y₂)
  | wrapMulLeft {x₁ x₂ y₁ : STerm}
      (hstatus : K.status .wrap = .mul)
      (vc : NativeVariableCondition (.wrap x₁ x₂) (.wrap y₁ x₂))
      (hweight : nativeKBOWeight K (.wrap x₁ x₂) = nativeKBOWeight K (.wrap y₁ x₂))
      (harg : NativeKBOGt K x₁ y₁) : NativeKBOGt K (.wrap x₁ x₂) (.wrap y₁ x₂)
  | wrapMulRight {x₁ x₂ y₂ : STerm}
      (hstatus : K.status .wrap = .mul)
      (vc : NativeVariableCondition (.wrap x₁ x₂) (.wrap x₁ y₂))
      (hweight : nativeKBOWeight K (.wrap x₁ x₂) = nativeKBOWeight K (.wrap x₁ y₂))
      (harg : NativeKBOGt K x₂ y₂) : NativeKBOGt K (.wrap x₁ x₂) (.wrap x₁ y₂)
  | recurFirstLex {b₁ s₁ n₁ b₂ s₂ n₂ : STerm}
      (hstatus : K.status .recur = .lex)
      (vc : NativeVariableCondition (.recur b₁ s₁ n₁) (.recur b₂ s₂ n₂))
      (hweight : nativeKBOWeight K (.recur b₁ s₁ n₁) = nativeKBOWeight K (.recur b₂ s₂ n₂))
      (harg : NativeKBOGt K b₁ b₂) : NativeKBOGt K (.recur b₁ s₁ n₁) (.recur b₂ s₂ n₂)
  | recurSecondLex {b s₁ n₁ s₂ n₂ : STerm}
      (hstatus : K.status .recur = .lex)
      (vc : NativeVariableCondition (.recur b s₁ n₁) (.recur b s₂ n₂))
      (hweight : nativeKBOWeight K (.recur b s₁ n₁) = nativeKBOWeight K (.recur b s₂ n₂))
      (harg : NativeKBOGt K s₁ s₂) : NativeKBOGt K (.recur b s₁ n₁) (.recur b s₂ n₂)
  | recurThirdLex {b s n₁ n₂ : STerm}
      (hstatus : K.status .recur = .lex)
      (vc : NativeVariableCondition (.recur b s n₁) (.recur b s n₂))
      (hweight : nativeKBOWeight K (.recur b s n₁) = nativeKBOWeight K (.recur b s n₂))
      (harg : NativeKBOGt K n₁ n₂) : NativeKBOGt K (.recur b s n₁) (.recur b s n₂)

/-- Every native status-KBO comparison carries the variable condition. -/
theorem NativeKBOGt.variableCondition {K : NativeKBOData} {x y : STerm}
    (h : NativeKBOGt K x y) : NativeVariableCondition x y := by
  cases h <;> assumption

/-- The compatible native status-KBO relation is closed under contexts and
substitutions by construction and retains the variable condition. -/
abbrev CompatibleNativeKBOGt (K : NativeKBOData) := CompatibleClosure (NativeKBOGt K)

theorem CompatibleNativeKBOGt.variableCondition {K : NativeKBOData} {x y : STerm}
    (h : CompatibleNativeKBOGt K x y) : NativeVariableCondition x y :=
  CompatibleClosure.variableCondition NativeKBOGt.variableCondition h

/-- No status-aware KBO comparison, including its context/substitution closure,
can orient the duplicating schema rule. -/
theorem nativeKBOWithStatus_blocks_dup (K : NativeKBOData) :
    ¬ CompatibleNativeKBOGt K dupSrc dupTgt := by
  intro h
  have hs := CompatibleNativeKBOGt.variableCondition h SchemaVar.s
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- Concrete admissible method with a genuine multiset status on `wrap`. -/
def nativeKBOWithStatusWitness : NativeKBOData where
  variableWeight := 1
  variableWeight_pos := by decide
  symbolWeight
    | .base => 1
    | .succ => 0
    | .wrap => 1
    | .recur => 1
  constantWeight_ge_variable := by decide
  precedenceRank
    | .base => 0
    | .wrap => 1
    | .recur => 2
    | .succ => 3
  precedenceRank_injective := by
    intro a b h
    cases a <;> cases b <;> simp_all
  status
    | .wrap => .mul
    | _ => .lex
  zeroWeightOnlySucc := by
    intro f h
    cases f <;> simp_all
  zeroWeightSuccMaximal := by
    intro _ f hf
    cases f <;> simp_all

/-- Strict-weight and equal-weight precedence branches are both inhabited. -/
theorem nativeKBOWithStatus_branch_controls :
    NativeKBOGt nativeKBOWithStatusWitness (.wrap .base .base) .base ∧
      NativeKBOGt nativeKBOWithStatusWitness (.succ .base) .base := by
  constructor
  · apply NativeKBOGt.weight
    · intro v
      cases v <;> simp [countVar]
    · decide
  · apply NativeKBOGt.precedence
    · intro v
      cases v <;> simp [countVar]
    · rfl
    · decide

/-- A concrete multiset-status branch is inhabited and consumes the stored
`wrap = mul` status. -/
theorem nativeKBOWithStatus_multiset_branch :
    NativeKBOGt nativeKBOWithStatusWitness
      (.wrap (.succ .base) .base) (.wrap .base .base) := by
  apply NativeKBOGt.wrapMulLeft
  · rfl
  · intro v
    cases v <;> simp [countVar]
  · rfl
  · exact nativeKBOWithStatus_branch_controls.2

/-- The strict-weight fragment is well founded by the method's actual weight. -/
def NativeKBOStrictWeightGt (K : NativeKBOData) (x y : STerm) : Prop :=
  NativeVariableCondition x y ∧ nativeKBOWeight K y < nativeKBOWeight K x

theorem nativeKBOStrictWeightGt_wellFounded (K : NativeKBOData) :
    WellFounded (fun y x : STerm => NativeKBOStrictWeightGt K x y) := by
  apply Subrelation.wf
    (r := fun y x : STerm => nativeKBOWeight K y < nativeKBOWeight K x)
  · intro y x h
    exact h.2
  · exact InvImage.wf (nativeKBOWeight K) Nat.lt_wfRel.wf

/-! ## Generalized KBO -/

/-- Generalized KBO data over a commutative semiring. The strict carrier order
and its additive compatibility are explicit admissibility laws. -/
structure GeneralizedKBOData (K : Type) [CommSemiring K] where
  variableWeight : K
  symbolWeight : MethodSymbol → K
  quasiPrecedence : MethodSymbol → Nat
  strict : K → K → Prop
  strict_wf : WellFounded strict
  strict_add_right : ∀ {a b}, strict a b → ∀ c, strict (a + c) (b + c)
  strict_add_left : ∀ {a b}, strict a b → ∀ c, strict (c + a) (c + b)

/-- Generalized semiring weight. -/
@[simp] def generalizedKBOWeight {K : Type} [CommSemiring K]
    (G : GeneralizedKBOData K) : STerm → K
  | .var _ => G.variableWeight
  | .base => G.symbolWeight .base
  | .succ t => G.symbolWeight .succ + generalizedKBOWeight G t
  | .wrap x y => G.symbolWeight .wrap + generalizedKBOWeight G x + generalizedKBOWeight G y
  | .recur b s n =>
      G.symbolWeight .recur + generalizedKBOWeight G b + generalizedKBOWeight G s +
        generalizedKBOWeight G n

/-- Quasi-precedence rank of a root. -/
def generalizedRootRank {K : Type} [CommSemiring K]
    (G : GeneralizedKBOData K) : STerm → Nat
  | .var _ => 0
  | t => match methodRoot t with
    | none => 0
    | some f => G.quasiPrecedence f + 1

/-- Generalized KBO comparison from semiring weight and quasi-precedence. -/
def GeneralizedKBOGt {K : Type} [CommSemiring K]
    (G : GeneralizedKBOData K) (x y : STerm) : Prop :=
  NativeVariableCondition x y ∧
    (G.strict (generalizedKBOWeight G y) (generalizedKBOWeight G x) ∨
      (generalizedKBOWeight G x = generalizedKBOWeight G y ∧
        generalizedRootRank G y < generalizedRootRank G x))

/-- Generalized KBO is well founded by the pair of semiring weight and
quasi-precedence. -/
theorem generalizedKBOGt_wellFounded {K : Type} [CommSemiring K]
    (G : GeneralizedKBOData K) :
    WellFounded (fun y x : STerm => GeneralizedKBOGt G x y) := by
  have hlex : WellFounded (Prod.Lex G.strict (fun a b : Nat => a < b)) :=
    WellFounded.prod_lex G.strict_wf Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage (Prod.Lex G.strict (fun a b : Nat => a < b))
      (fun t => (generalizedKBOWeight G t, generalizedRootRank G t)))
  · intro y x h
    rcases h.2 with hw | ⟨heq, hp⟩
    · exact Prod.Lex.left _ _ hw
    · change Prod.Lex G.strict (fun a b : Nat => a < b)
        (generalizedKBOWeight G y, generalizedRootRank G y)
        (generalizedKBOWeight G x, generalizedRootRank G x)
      rw [heq]
      exact Prod.Lex.right _ hp
  · exact InvImage.wf
      (fun t => (generalizedKBOWeight G t, generalizedRootRank G t)) hlex

/-- The variable condition gives the same exact duplicator obstruction. -/
theorem generalizedKBO_blocks_dup {K : Type} [CommSemiring K]
    (G : GeneralizedKBOData K) : ¬ GeneralizedKBOGt G dupSrc dupTgt := by
  intro h
  have hs := h.1 SchemaVar.s
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- Concrete generalized KBO with a collapsing quasi-precedence. -/
def generalizedNatKBOWitness : GeneralizedKBOData Nat where
  variableWeight := 1
  symbolWeight := fun _ => 1
  quasiPrecedence
    | .base => 0
    | .succ => 0
    | .wrap => 1
    | .recur => 2
  strict := (· < ·)
  strict_wf := Nat.lt_wfRel.wf
  strict_add_right := by intro a b h c; omega
  strict_add_left := by intro a b h c; omega

/-! ## AC KBO -/

/-- Variable occurrence counts are invariant under the full symmetric,
transitive AC equivalence generated by `ACRearrange`. -/
theorem countVar_acRearrange_eqv {x y : STerm}
    (h : Relation.EqvGen ACRearrange x y) (v : SchemaVar) :
    countVar v x = countVar v y := by
  induction h with
  | rel _ _ hxy => exact countVar_acRearrange hxy v
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- AC-KBO compares AC-equivalent representatives using the native
status-aware KBO relation. -/
def NativeACKBOGt (K : NativeKBOData) (x y : STerm) : Prop :=
  ∃ x' y', Relation.EqvGen ACRearrange x x' ∧
    Relation.EqvGen ACRearrange y y' ∧ NativeKBOGt K x' y'

/-- AC-KBO retains the variable condition because AC equivalence preserves all
variable counts in both directions. -/
theorem nativeACKBO_variableCondition {K : NativeKBOData} {x y : STerm}
    (h : NativeACKBOGt K x y) : NativeVariableCondition x y := by
  rcases h with ⟨x', y', hx, hy, hgt⟩
  intro v
  have hv := NativeKBOGt.variableCondition hgt v
  have hxv := countVar_acRearrange_eqv hx v
  have hyv := countVar_acRearrange_eqv hy v
  rw [hxv, hyv]
  exact hv

/-- Native AC-KBO blocks the duplicator for the same load-bearing reason. -/
theorem nativeACKBO_blocks_dup (K : NativeKBOData) : ¬ NativeACKBOGt K dupSrc dupTgt := by
  intro h
  have hs := nativeACKBO_variableCondition h SchemaVar.s
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- Nontrivial AC equivalence control retained from the actual method theory. -/
theorem nativeACKBO_ac_control :
    Relation.EqvGen ACRearrange
      (.wrap (.var SchemaVar.b) (.var SchemaVar.s))
      (.wrap (.var SchemaVar.s) (.var SchemaVar.b)) :=
  Relation.EqvGen.rel _ _ (ACRearrange.commWrap _ _)

/-! ## Transfinite KBO -/

/-- Actual ordinal weights and finite root precedence. -/
structure NativeTransfiniteKBO where
  variableWeight : Ordinal
  symbolWeight : MethodSymbol → Ordinal
  precedenceRank : MethodSymbol → Nat

/-- Ordinal-valued additive weight. -/
noncomputable def transfiniteKBOWeight (T : NativeTransfiniteKBO) : STerm → Ordinal
  | .var _ => T.variableWeight
  | .base => T.symbolWeight .base
  | .succ t => T.symbolWeight .succ + transfiniteKBOWeight T t
  | .wrap x y => T.symbolWeight .wrap + transfiniteKBOWeight T x + transfiniteKBOWeight T y
  | .recur b s n =>
      T.symbolWeight .recur + transfiniteKBOWeight T b + transfiniteKBOWeight T s +
        transfiniteKBOWeight T n

/-- Root rank for the ordinal KBO. -/
def transfiniteRootRank (T : NativeTransfiniteKBO) : STerm → Nat
  | .var _ => 0
  | t => match methodRoot t with
    | none => 0
    | some f => T.precedenceRank f + 1

/-- Transfinite KBO comparison. -/
def TransfiniteKBOGt (T : NativeTransfiniteKBO) (x y : STerm) : Prop :=
  NativeVariableCondition x y ∧
    (transfiniteKBOWeight T y < transfiniteKBOWeight T x ∨
      (transfiniteKBOWeight T x = transfiniteKBOWeight T y ∧
        transfiniteRootRank T y < transfiniteRootRank T x))

/-- Transfinite KBO is well founded by ordinal weight then finite precedence. -/
theorem transfiniteKBOGt_wellFounded (T : NativeTransfiniteKBO) :
    WellFounded (fun y x : STerm => TransfiniteKBOGt T x y) := by
  have hlex : WellFounded
      (Prod.Lex (fun a b : Ordinal => a < b) (fun a b : Nat => a < b)) :=
    WellFounded.prod_lex wellFounded_lt Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (fun a b : Ordinal => a < b) (fun a b : Nat => a < b))
      (fun t => (transfiniteKBOWeight T t, transfiniteRootRank T t)))
  · intro y x h
    rcases h.2 with hw | ⟨heq, hp⟩
    · exact Prod.Lex.left _ _ hw
    · change Prod.Lex (fun a b : Ordinal => a < b) (fun a b : Nat => a < b)
        (transfiniteKBOWeight T y, transfiniteRootRank T y)
        (transfiniteKBOWeight T x, transfiniteRootRank T x)
      rw [heq]
      exact Prod.Lex.right _ hp
  · exact InvImage.wf
      (fun t => (transfiniteKBOWeight T t, transfiniteRootRank T t)) hlex

/-- Ordinal weights do not change the variable-condition obstruction. -/
theorem transfiniteKBO_blocks_dup (T : NativeTransfiniteKBO) :
    ¬ TransfiniteKBOGt T dupSrc dupTgt := by
  intro h
  have hs := h.1 SchemaVar.s
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- Concrete ordinal-weight method. -/
noncomputable def nativeTransfiniteKBOWitness : NativeTransfiniteKBO where
  variableWeight := 1
  symbolWeight
    | .base => 1
    | .succ => Ordinal.omega0
    | .wrap => Ordinal.omega0 + 1
    | .recur => Ordinal.omega0 * 2
  precedenceRank
    | .base => 0
    | .succ => 1
    | .wrap => 2
    | .recur => 3

/-! ## Lambda-free applicative KBO -/

/-- Variable condition on the applicative encoding. -/
def AppVariableCondition (x y : AppTerm) : Prop :=
  ∀ v : SchemaVar, countVarApp v y ≤ countVarApp v x

/-- Native applicative KBO data. -/
structure NativeLambdaFreeKBO where
  variableWeight : Nat
  constantWeight : MethodSymbol → Nat
  applicationWeight : Nat
  constantPrecedence : MethodSymbol → Nat

/-- Applicative KBO weight. -/
@[simp] def lambdaFreeKBOWeight (K : NativeLambdaFreeKBO) : AppTerm → Nat
  | .var _ => K.variableWeight
  | .const f => K.constantWeight f
  | .app f a => K.applicationWeight + lambdaFreeKBOWeight K f + lambdaFreeKBOWeight K a

/-- Root precedence of an applicative term. -/
def lambdaFreeRootRank (K : NativeLambdaFreeKBO) : AppTerm → Nat
  | .const f => K.constantPrecedence f + 1
  | .app _ _ => 1
  | .var _ => 0

/-- Native lambda-free KBO comparison. -/
def LambdaFreeNativeKBOGt (K : NativeLambdaFreeKBO) (x y : AppTerm) : Prop :=
  AppVariableCondition x y ∧
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (lambdaFreeKBOWeight K y, lambdaFreeRootRank K y)
      (lambdaFreeKBOWeight K x, lambdaFreeRootRank K x)

/-- Applicative native KBO is well founded. -/
theorem lambdaFreeNativeKBOGt_wellFounded (K : NativeLambdaFreeKBO) :
    WellFounded (fun y x : AppTerm => LambdaFreeNativeKBOGt K x y) := by
  have hlex : WellFounded
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (fun t => (lambdaFreeKBOWeight K t, lambdaFreeRootRank K t)))
  · intro y x h
    exact h.2
  · exact InvImage.wf
      (fun t => (lambdaFreeKBOWeight K t, lambdaFreeRootRank K t)) hlex

/-- The currying translation retains the exact payload multiplicity, so the
native lambda-free KBO blocks the duplicating rule. -/
theorem lambdaFreeNativeKBO_blocks_dup (K : NativeLambdaFreeKBO) :
    ¬ LambdaFreeNativeKBOGt K (curry dupSrc) (curry dupTgt) := by
  intro h
  have hs := h.1 SchemaVar.s
  rw [countVarApp_curry, countVarApp_curry, countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- Concrete applicative method. -/
def nativeLambdaFreeKBOWitness : NativeLambdaFreeKBO where
  variableWeight := 1
  constantWeight := fun _ => 1
  applicationWeight := 1
  constantPrecedence
    | .base => 0
    | .succ => 1
    | .wrap => 2
    | .recur => 3

/-! ## Polynomial KBO -/

/-- Polynomial weight functions are the method data; monotonicity is the
admissibility law used by constructor extensions. -/
structure NativePolynomialKBO where
  variableWeight : Nat
  weightPoly : MethodSymbol → Nat → Nat
  precedenceRank : MethodSymbol → Nat
  weightPoly_mono : ∀ f {a b}, a ≤ b → weightPoly f a ≤ weightPoly f b

/-- Polynomial term weight computed recursively from the method's functions. -/
@[simp] def polynomialKBOTermWeight (P : NativePolynomialKBO) : STerm → Nat
  | .var _ => P.variableWeight
  | .base => P.weightPoly .base 0
  | .succ t => P.weightPoly .succ (polynomialKBOTermWeight P t)
  | .wrap x y => P.weightPoly .wrap
      (polynomialKBOTermWeight P x + polynomialKBOTermWeight P y)
  | .recur b s n => P.weightPoly .recur
      (polynomialKBOTermWeight P b + polynomialKBOTermWeight P s + polynomialKBOTermWeight P n)

/-- Polynomial-KBO root precedence. -/
def polynomialKBORootRank (P : NativePolynomialKBO) : STerm → Nat
  | .var _ => 0
  | t => match methodRoot t with
    | none => 0
    | some f => P.precedenceRank f + 1

/-- Native polynomial KBO comparison. -/
def PolynomialNativeKBOGt (P : NativePolynomialKBO) (x y : STerm) : Prop :=
  NativeVariableCondition x y ∧
    Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (polynomialKBOTermWeight P y, polynomialKBORootRank P y)
      (polynomialKBOTermWeight P x, polynomialKBORootRank P x)

/-- Native polynomial KBO is well founded. -/
theorem polynomialNativeKBOGt_wellFounded (P : NativePolynomialKBO) :
    WellFounded (fun y x : STerm => PolynomialNativeKBOGt P x y) := by
  have hlex : WellFounded
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)) :=
    WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  apply Subrelation.wf
    (r := InvImage
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (fun t => (polynomialKBOTermWeight P t, polynomialKBORootRank P t)))
  · intro y x h
    exact h.2
  · exact InvImage.wf
      (fun t => (polynomialKBOTermWeight P t, polynomialKBORootRank P t)) hlex

/-- Polynomial weights cannot remove the variable-condition obstruction. -/
theorem polynomialNativeKBO_blocks_dup (P : NativePolynomialKBO) :
    ¬ PolynomialNativeKBOGt P dupSrc dupTgt := by
  intro h
  have hs := h.1 SchemaVar.s
  rw [countVar_dupSrc_s, countVar_dupTgt_s] at hs
  omega

/-- Nonlinear polynomial weight function used by the concrete witness. -/
def nativePolynomialWeight (_ : MethodSymbol) (n : Nat) : Nat := n * n + n + 1

/-- The nonlinear weight function is monotone. -/
theorem nativePolynomialWeight_mono (f : MethodSymbol) {a b : Nat} (h : a ≤ b) :
    nativePolynomialWeight f a ≤ nativePolynomialWeight f b := by
  simp [nativePolynomialWeight]
  nlinarith

/-- Concrete polynomial KBO with a genuinely nonlinear weight function. -/
def nativePolynomialKBOWitness : NativePolynomialKBO where
  variableWeight := 1
  weightPoly := nativePolynomialWeight
  precedenceRank
    | .base => 0
    | .succ => 1
    | .wrap => 2
    | .recur => 3
  weightPoly_mono := nativePolynomialWeight_mono

/-- The nonlinear polynomial function is active on a concrete argument. -/
theorem nativePolynomialKBOWitness_nonlinear_control :
    nativePolynomialKBOWitness.weightPoly .succ 2 = 7 := by
  rfl

/-! ## Existing native RPO, permutation, POP* and simple-order controls -/

/-- The AC-RPO source already carries a nontrivial AC equivalence, a strict
well-founded order, root orientation and full-context orientation. -/
abbrev NativeACRPOControl : Prop := ACRPORowClaim

/-- The permutation-modular RPO source carries a nonidentity binary status and
proves compatibility of that status with the same equational order. -/
abbrev NativePermutationRPOControl : Prop := RPOModuloPermutationRowClaim

/-- POP* uses the actual safe/normal assignment and fails the exact safe
linearity condition at the duplicated payload. -/
abbrev NativePOPStarControl : Prop := PopStarFamilyRowClaim

/-- The simple-termination row retains the compiled context-compatible LPO and
its well-foundedness, together with the direct affine obstruction. -/
abbrev NativeSimpleTerminationControl : Prop := SimpleTerminationOrderTypeRowClaim

/-! ## ORI-1 capstone -/

/-- Native semantics for all ten ORI-1 rows. -/
structure ORI1NativeSemantics where
  kboWithStatus : NativeKBOData
  kboWithStatusBlocked : ¬ CompatibleNativeKBOGt kboWithStatus dupSrc dupTgt
  kboWithStatusWeightWF : WellFounded
    (fun y x : STerm => NativeKBOStrictWeightGt kboWithStatus x y)
  statusBranch : NativeKBOGt kboWithStatus
    (.wrap (.succ .base) .base) (.wrap .base .base)
  generalized : GeneralizedKBOData Nat
  generalizedWF : WellFounded (fun y x : STerm => GeneralizedKBOGt generalized x y)
  generalizedBlocked : ¬ GeneralizedKBOGt generalized dupSrc dupTgt
  acBlocked : ¬ NativeACKBOGt kboWithStatus dupSrc dupTgt
  acTheoryNontrivial : Relation.EqvGen ACRearrange
    (.wrap (.var SchemaVar.b) (.var SchemaVar.s))
    (.wrap (.var SchemaVar.s) (.var SchemaVar.b))
  transfinite : NativeTransfiniteKBO
  transfiniteWF : WellFounded (fun y x : STerm => TransfiniteKBOGt transfinite x y)
  transfiniteBlocked : ¬ TransfiniteKBOGt transfinite dupSrc dupTgt
  lambdaFree : NativeLambdaFreeKBO
  lambdaFreeWF : WellFounded
    (fun y x : AppTerm => LambdaFreeNativeKBOGt lambdaFree x y)
  lambdaFreeBlocked : ¬ LambdaFreeNativeKBOGt lambdaFree (curry dupSrc) (curry dupTgt)
  polynomial : NativePolynomialKBO
  polynomialWF : WellFounded
    (fun y x : STerm => PolynomialNativeKBOGt polynomial x y)
  polynomialBlocked : ¬ PolynomialNativeKBOGt polynomial dupSrc dupTgt
  acRPO : NativeACRPOControl
  acRPOOrder : EquationalPathOrderCertificate
  acRPOOrderNontrivial :
    acRPOOrder.equiv (.app .void (.delta .void)) (.app (.delta .void) .void)
  permutationRPO : NativePermutationRPOControl
  permutationRPOData : PermutationRPOCertificate
  permutationRPOStatusNonidentity :
    permutationRPOData.status.perm .app ≠ Equiv.refl (Fin 2)
  popStar : NativePOPStarControl
  popStarArgKind : OperatorKO7.MetaLPO.KO7Sym → Nat → ArgKind
  popStarArgKindExact : popStarArgKind = ko7ArgKind
  popStarNoCertificate : ¬ Nonempty KO7POPStarCertificate
  simpleTermination : NativeSimpleTerminationControl
  simpleTerminationOrder : EquationalPathOrderCertificate
  simpleTerminationWF : WellFounded (fun y x : Trace => simpleTerminationOrder.gt x y)

/-- Concrete ORI-1 native-method package. -/
noncomputable def ori1NativeSemantics : ORI1NativeSemantics where
  kboWithStatus := nativeKBOWithStatusWitness
  kboWithStatusBlocked := nativeKBOWithStatus_blocks_dup _
  kboWithStatusWeightWF := nativeKBOStrictWeightGt_wellFounded _
  statusBranch := nativeKBOWithStatus_multiset_branch
  generalized := generalizedNatKBOWitness
  generalizedWF := generalizedKBOGt_wellFounded _
  generalizedBlocked := generalizedKBO_blocks_dup _
  acBlocked := nativeACKBO_blocks_dup _
  acTheoryNontrivial := nativeACKBO_ac_control
  transfinite := nativeTransfiniteKBOWitness
  transfiniteWF := transfiniteKBOGt_wellFounded _
  transfiniteBlocked := transfiniteKBO_blocks_dup _
  lambdaFree := nativeLambdaFreeKBOWitness
  lambdaFreeWF := lambdaFreeNativeKBOGt_wellFounded _
  lambdaFreeBlocked := lambdaFreeNativeKBO_blocks_dup _
  polynomial := nativePolynomialKBOWitness
  polynomialWF := polynomialNativeKBOGt_wellFounded _
  polynomialBlocked := polynomialNativeKBO_blocks_dup _
  acRPO := acRPO_row_anchor
  acRPOOrder := ko7AppACReductionOrder
  acRPOOrderNontrivial := ko7AppACReductionOrder_nontrivial.1
  permutationRPO := rpoModuloPermutation_row_anchor
  permutationRPOData := ko7PermutationRPO
  permutationRPOStatusNonidentity := swapAppPermutationStatus_nonidentity
  popStar := popStarFamily_row_anchor
  popStarArgKind := ko7ArgKind
  popStarArgKindExact := rfl
  popStarNoCertificate := no_ko7POPStarCertificate
  simpleTermination := simpleTerminationOrderType_row_anchor
  simpleTerminationOrder := ko7EmptyEquationalRPO
  simpleTerminationWF := ko7EmptyEquationalRPO.gt_wellFounded

end OperatorKO7.Methods.OrientationClosure.PathOrderNativeSemantics
