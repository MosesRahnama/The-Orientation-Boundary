import OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms

/-!
# Constructed finite adapters for first-order rewrite systems

`FiniteCoordinateAlgorithms.TRSFiniteAdapter` has four hypotheses: an injective
realization, step preservation, step reflection, and reduction closure. This
file constructs an adapter for every rewrite system whose rules rewrite one
nullary symbol to another, over any explicit enumeration of the signature. Two
controls follow. The fork `s → a`, `s → b`, `a → c`, `b → c` joins `a` and `b`
through `c`, while the table observed on `{s, a, b}` has no common reduct and
admits no adapter. The one-rule system `f(x) → f(S x)` has no finite adapter
that realizes any term `f(t)`.
-/

namespace OperatorKO7.Meta.OperationalInexpressibility.TRSFiniteAdapterInstances

open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms
open OperatorKO7.Meta.Rewriting

universe u v w

section Constant

variable {sigma : Type u} {nu : Type v}

/-- The term formed by a nullary symbol. -/
def constTerm (f : sigma) : Term sigma nu := .app f []

/-- A rewrite system whose rules all rewrite one nullary symbol to another. -/
def ConstantTRS (R : TRS sigma nu) : Prop :=
  ∀ rule ∈ R, ∃ f g : sigma, rule.lhs = constTerm f ∧ rule.rhs = constTerm g

/-- Symbol-level edge relation: some rule rewrites the constant `f` to the
constant `g`. -/
def ConstEdge (R : TRS sigma nu) (f g : sigma) : Prop :=
  ∃ rule ∈ R, rule.lhs = constTerm f ∧ rule.rhs = constTerm g

theorem constTerm_injective : Function.Injective (constTerm : sigma → Term sigma nu) := by
  intro f g h
  exact (Term.app.inj h).1

@[simp] theorem rename_constTerm {nu' : Type w} (g : nu → nu') (f : sigma) :
    Term.rename g (constTerm f : Term sigma nu) = constTerm f := rfl

@[simp] theorem apply_constTerm (s : Subst sigma nu) (f : sigma) :
    Subst.apply s (constTerm f : Term sigma nu) = constTerm f := rfl

variable [DecidableEq nu]

/-- For a constant system, the one-step reducts of a constant in the renamed
system are exactly the constants reached by one rule. -/
theorem step_constTerm_iff {R : TRS sigma nu} (hR : ConstantTRS R) (f : sigma)
    (t : Term sigma (RenVar nu)) :
    Step (renameTRS R) (constTerm f) t ↔ ∃ g, ConstEdge R f g ∧ t = constTerm g := by
  constructor
  · intro h
    generalize hs : (constTerm f : Term sigma (RenVar nu)) = s at h
    cases h with
    | root hroot =>
        obtain ⟨rule, hmem, σ, hl, hr⟩ := hroot
        subst hs
        simp only [renameTRS, List.mem_append, List.mem_map] at hmem
        rcases hmem with ⟨r, hrR, rfl⟩ | ⟨r, hrR, rfl⟩
        · obtain ⟨f0, g0, hl0, hr0⟩ := hR r hrR
          rw [renameRule_lhs, hl0, rename_constTerm, apply_constTerm] at hl
          rw [renameRule_rhs, hr0, rename_constTerm, apply_constTerm] at hr
          obtain rfl := constTerm_injective hl
          exact ⟨g0, ⟨r, hrR, hl0, hr0⟩, hr⟩
        · obtain ⟨f0, g0, hl0, hr0⟩ := hR r hrR
          rw [renameRule_lhs, hl0, rename_constTerm, apply_constTerm] at hl
          rw [renameRule_rhs, hr0, rename_constTerm, apply_constTerm] at hr
          obtain rfl := constTerm_injective hl
          exact ⟨g0, ⟨r, hrR, hl0, hr0⟩, hr⟩
    | arg f' pre post h' =>
        simp [constTerm] at hs
  · rintro ⟨g, ⟨r, hrR, hl0, hr0⟩, rfl⟩
    refine Step.root ⟨renameRule Sum.inl r, renameRule_inl_mem hrR, Subst.id, ?_, ?_⟩
    · rw [renameRule_lhs, hl0, rename_constTerm, apply_constTerm]
    · rw [renameRule_rhs, hr0, rename_constTerm, apply_constTerm]

variable [DecidableEq sigma]

/-- Boolean edge test for `ConstEdge`. -/
def constEdgeB (R : TRS sigma nu) (f g : sigma) : Bool :=
  R.any fun rule => decide (rule.lhs = constTerm f) && decide (rule.rhs = constTerm g)

theorem constEdgeB_eq_true_iff (R : TRS sigma nu) (f g : sigma) :
    constEdgeB R f g = true ↔ ConstEdge R f g := by
  simp [constEdgeB, ConstEdge]

/-- P4.3: the finite adapter of a constant rewrite system over an explicit
enumeration of its signature. States are symbols, a symbol is realized by its
constant term, and the edge table lists the rules. -/
def constantAdapter (E : Enumeration sigma) (R : TRS sigma nu) (hR : ConstantTRS R) :
    TRSFiniteAdapter R sigma where
  table := ⟨E, constEdgeB R⟩
  realize f := constTerm f
  realize_injective := constTerm_injective
  step_sound := by
    intro a b h
    exact (step_constTerm_iff hR a (constTerm b)).2 ⟨b, (constEdgeB_eq_true_iff R a b).1 h, rfl⟩
  step_reflect := by
    intro a b h
    obtain ⟨g, hg, heq⟩ := (step_constTerm_iff hR a (constTerm b)).1 h
    obtain rfl := constTerm_injective heq
    exact (constEdgeB_eq_true_iff R a b).2 hg
  reduction_closed := by
    intro a t h
    obtain ⟨g, -, rfl⟩ := (step_constTerm_iff hR a t).1 h
    exact ⟨g, rfl⟩

/-- For a constant system, reachability of constants in the renamed rewrite
system is reachability in the symbol-level edge relation. -/
theorem constant_reach_iff (E : Enumeration sigma) {R : TRS sigma nu} (hR : ConstantTRS R)
    (f g : sigma) :
    Relation.ReflTransGen (ConstEdge R) f g ↔
      StepStar (renameTRS R) (constTerm f) (constTerm g) := by
  have hrel : (constantAdapter E R hR).table.Step = ConstEdge R := by
    funext a b
    exact propext (constEdgeB_eq_true_iff R a b)
  rw [← hrel]
  exact (constantAdapter E R hR).reach_iff f g

end Constant

/-! ## Control: the fork `s → a`, `s → b`, `a → c`, `b → c` -/

/-- Symbols of the fork control. -/
inductive ForkSym where
  | s | a | b | c
  deriving DecidableEq, Repr

/-- Explicit enumeration of the fork symbols. -/
def forkEnumeration : Enumeration ForkSym where
  items := [.s, .a, .b, .c]
  nodup := by decide
  complete := by
    intro x
    cases x <;> decide

/-- The rule rewriting the constant `f` to the constant `g`. -/
def constRule (f g : ForkSym) : Rule ForkSym Empty := ⟨constTerm f, constTerm g, rfl⟩

/-- The fork `s → a`, `s → b`, `a → c`, `b → c`. -/
def forkTRS : TRS ForkSym Empty :=
  [constRule .s .a, constRule .s .b, constRule .a .c, constRule .b .c]

theorem forkTRS_constant : ConstantTRS forkTRS := by
  intro rule hrule
  simp [forkTRS] at hrule
  rcases hrule with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, rfl⟩

/-- The adapter of the fork over all four symbols. -/
def forkAdapter : TRSFiniteAdapter forkTRS ForkSym :=
  constantAdapter forkEnumeration forkTRS forkTRS_constant

/-- Control: the full relation joins `a` and `b` at `c`. -/
theorem fork_joinable_a_b :
    joinable (renameTRS forkTRS) (constTerm ForkSym.a : Term ForkSym (RenVar Empty))
      (constTerm ForkSym.b) := by
  refine (forkAdapter.joinable_iff .a .b).1 ⟨.c, ?_, ?_⟩
  · exact Relation.ReflTransGen.single
      ((constEdgeB_eq_true_iff forkTRS .a .c).2 ⟨constRule .a .c, by simp [forkTRS], rfl, rfl⟩)
  · exact Relation.ReflTransGen.single
      ((constEdgeB_eq_true_iff forkTRS .b .c).2 ⟨constRule .b .c, by simp [forkTRS], rfl, rfl⟩)

/-- The fork states observed without `c`. -/
inductive ForkObs where
  | s | a | b
  deriving DecidableEq, Repr

/-- Explicit enumeration of the observed states. -/
def forkObsEnumeration : Enumeration ForkObs where
  items := [.s, .a, .b]
  nodup := by decide
  complete := by
    intro x
    cases x <;> decide

/-- Realization of the observed states as fork constants. -/
def forkObsRealize : ForkObs → Term ForkSym (RenVar Empty)
  | .s => constTerm .s
  | .a => constTerm .a
  | .b => constTerm .b

/-- The observed edge table: the two edges out of `s`. -/
def forkObsTable : RelationTable ForkObs where
  explicit := forkObsEnumeration
  stepB x y := match x, y with
    | .s, .a => true
    | .s, .b => true
    | _, _ => false

theorem eq_of_reflTransGen_of_forall_not {α : Type u} {r : α → α → Prop} {x z : α}
    (h : Relation.ReflTransGen r x z) (hx : ∀ y, ¬ r x y) : z = x := by
  rcases Relation.ReflTransGen.cases_head_iff.1 h with rfl | ⟨c, hxc, -⟩
  · rfl
  · exact absurd hxc (hx c)

/-- Control: in the observed table, `a` and `b` have no common reduct. -/
theorem forkObs_not_joinable :
    ¬ ∃ z, Relation.ReflTransGen forkObsTable.Step .a z ∧
      Relation.ReflTransGen forkObsTable.Step .b z := by
  rintro ⟨z, ha, hb⟩
  have hna : ∀ y, ¬ forkObsTable.Step .a y := by
    intro y
    cases y <;> simp [RelationTable.Step, forkObsTable]
  have hnb : ∀ y, ¬ forkObsTable.Step .b y := by
    intro y
    cases y <;> simp [RelationTable.Step, forkObsTable]
  have hza := eq_of_reflTransGen_of_forall_not ha hna
  have hzb := eq_of_reflTransGen_of_forall_not hb hnb
  rw [hza] at hzb
  cases hzb

/-- Control: the observed table is not reduction closed, since `a` rewrites to
`c` and no observed state realizes `c`. -/
theorem forkObs_not_reductionClosed :
    Step (renameTRS forkTRS) (forkObsRealize .a) (constTerm .c) ∧
      ∀ y, forkObsRealize y ≠ constTerm .c := by
  refine ⟨(step_constTerm_iff forkTRS_constant .a (constTerm .c)).2
    ⟨.c, ⟨constRule .a .c, by simp [forkTRS], rfl, rfl⟩, rfl⟩, ?_⟩
  intro y hy
  cases y <;> exact absurd (constTerm_injective hy) (by decide)

/-- Control: no adapter of the fork has the observed realization. -/
theorem forkObs_no_adapter (A : TRSFiniteAdapter forkTRS ForkObs) :
    A.realize ≠ forkObsRealize := by
  intro hA
  obtain ⟨hstep, hnone⟩ := forkObs_not_reductionClosed
  rw [← hA] at hstep
  obtain ⟨y, hy⟩ := A.reduction_closed hstep
  rw [hA] at hy
  exact hnone y hy

/-! ## Control: the orbit `f(x) → f(S x)` -/

/-- Symbols of the orbit control. -/
inductive OrbitSym where
  | f | S
  deriving DecidableEq, Repr

/-- The rule `f(x) → f(S x)`. -/
def orbitRule : Rule OrbitSym Unit :=
  ⟨.app .f [.var ()], .app .f [.app .S [.var ()]], rfl⟩

/-- The one-rule orbit system. -/
def orbitTRS : TRS OrbitSym Unit := [orbitRule]

/-- The symbol `S` applied `n` times. -/
def sPow (t : Term OrbitSym (RenVar Unit)) : Nat → Term OrbitSym (RenVar Unit)
  | 0 => t
  | n + 1 => .app .S [sPow t n]

theorem size_sPow (t : Term OrbitSym (RenVar Unit)) (n : Nat) :
    (sPow t n).size = n + t.size := by
  induction n with
  | zero => simp [sPow]
  | succ n ih =>
      simp only [sPow, Term.size_app, Term.sizeList_cons, Term.sizeList_nil, ih]
      omega

theorem sPow_injective (t : Term OrbitSym (RenVar Unit)) : Function.Injective (sPow t) := by
  intro n m h
  have hsize := congrArg Term.size h
  rw [size_sPow, size_sPow] at hsize
  omega

theorem orbit_step (u : Term OrbitSym (RenVar Unit)) :
    Step (renameTRS orbitTRS) (.app .f [u]) (.app .f [.app .S [u]]) :=
  Step.root ⟨renameRule Sum.inl orbitRule, renameRule_inl_mem (by simp [orbitTRS]),
    fun _ => u, rfl, rfl⟩

theorem orbit_stepStar (t : Term OrbitSym (RenVar Unit)) (n : Nat) :
    StepStar (renameTRS orbitTRS) (.app .f [t]) (.app .f [sPow t n]) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih => exact Relation.ReflTransGen.tail ih (orbit_step (sPow t n))

/-- Control: no finite reduction-closed adapter of `f(x) → f(S x)` realizes a
term `f(t)`; the orbit `f(S^n t)` would need infinitely many states. -/
theorem orbit_no_adapter_realizes_f {α : Type w} [DecidableEq α]
    (A : TRSFiniteAdapter orbitTRS α) (a : α) (t : Term OrbitSym (RenVar Unit)) :
    A.realize a ≠ .app .f [t] := by
  intro ha
  have hex : ∀ n, ∃ b, A.realize b = .app .f [sPow t n] := by
    intro n
    have hreach : StepStar (renameTRS orbitTRS) (A.realize a) (.app .f [sPow t n]) := by
      rw [ha]
      exact orbit_stepStar t n
    obtain ⟨b, hb, -⟩ := A.reach_reflect hreach
    exact ⟨b, hb⟩
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro n m hnm
    have h := congrArg A.realize hnm
    rw [hg n, hg m] at h
    injection h with _ hargs
    injection hargs with hs _
    exact sPow_injective t hs
  haveI : Fintype α :=
    ⟨A.table.explicit.items.toFinset, fun x => List.mem_toFinset.2 (A.table.explicit.complete x)⟩
  exact not_injective_infinite_finite g hinj

end OperatorKO7.Meta.OperationalInexpressibility.TRSFiniteAdapterInstances
