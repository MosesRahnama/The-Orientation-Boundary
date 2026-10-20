import OperatorKO7.Meta.Impossibility_Lemmas

/-!
# Conjecture Boundary (Theorem-Level No-Go Statements)

This module collects theorem-level barriers proved by the KO7 artifact.

The purpose is narrower:
- record explicit impossibility theorems for concrete internal method families;
- keep these boundaries importable from one module.
-/

namespace OperatorKO7.MetaConjectureBoundary

open OperatorKO7 Trace
open OperatorKO7.Impossibility

/-! ## Global-orientation interface (full kernel Step) -/

/-- A measure/order pair globally orients the full kernel `Step`. -/
def GlobalOrients {α : Type} (m : Trace → α) (lt : α → α → Prop) : Prop :=
  ∀ {a b}, Step a b → lt (m b) (m a)

/-! ## Additive / Lex barriers -/

/-- No fixed additive bump on `kappa` can orient `rec_succ` uniformly. -/
theorem no_fixed_kappa_plus_k (k : Nat) :
    ¬ (∀ (b s n : Trace),
      FailedMeasures.kappa (app s (recΔ b s n)) + k <
      FailedMeasures.kappa (recΔ b s (delta n)) + k) :=
  FailedMeasures.kappa_plus_k_fails k

/-- The simple 2-component lex witness `(kappa, mu)` fails on KO7. -/
theorem no_simple_lex_witness :
    ¬ (∀ (b s n : Trace),
      Prod.Lex (· < ·) (· < ·)
        (FailedMeasures.kappa (app s (recΔ b s n)),
         FailedMeasures.mu (app s (recΔ b s n)))
        (FailedMeasures.kappa (recΔ b s (delta n)),
         FailedMeasures.mu (recΔ b s (delta n)))) :=
  FailedMeasures.simple_lex_fails

/-- Additive size cannot strictly decrease across all `rec_succ` instances. -/
theorem no_additive_strict_drop_rec_succ :
    ¬ (∀ (b s n : Trace),
      UncheckedRecursionFailure.simpleSize (app s (recΔ b s n)) <
      UncheckedRecursionFailure.simpleSize (recΔ b s (delta n))) := by
  intro h
  have hlt := h void void void
  have hge :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  exact Nat.not_lt_of_ge hge hlt

/-! ## Strengthened full-step no-go theorems -/

/-- No fixed additive bump can globally orient full `Step`. -/
theorem no_global_step_orientation_kappa_plus_k (k : Nat) :
    ¬ GlobalOrients (fun t => FailedMeasures.kappa t + k) (· < ·) := by
  intro h
  apply no_fixed_kappa_plus_k k
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Plain structural depth (`kappa`) cannot globally orient full `Step`. -/
theorem no_global_step_orientation_kappa :
    ¬ GlobalOrients FailedMeasures.kappa (· < ·) := by
  intro h
  apply no_fixed_kappa_plus_k 0
  intro b s n
  have hlt : FailedMeasures.kappa (app s (recΔ b s n)) <
      FailedMeasures.kappa (recΔ b s (delta n)) :=
    h (Step.R_rec_succ b s n)
  simp at hlt

/-- The simple lex witness `(kappa, mu)` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simple_lex :
    ¬ GlobalOrients
      (fun t => (FailedMeasures.kappa t, FailedMeasures.mu t))
      (Prod.Lex (· < ·) (· < ·)) := by
  intro h
  apply no_simple_lex_witness
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Additive `simpleSize` cannot globally orient full `Step`. -/
theorem no_global_step_orientation_simpleSize :
    ¬ GlobalOrients UncheckedRecursionFailure.simpleSize (· < ·) := by
  intro h
  apply no_additive_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-! ## Flag-only barrier -/

/-- A single top-level flag cannot globally orient full `Step`. -/
theorem no_global_flag_only_orientation :
    ¬ (∀ a b : Trace, Step a b →
      FlagFailure.deltaFlagTop b < FlagFailure.deltaFlagTop a) := by
  intro h
  let t : Trace := delta void
  have hstep : Step (merge void t) t := Step.R_merge_void_left t
  have hlt : FlagFailure.deltaFlagTop t < FlagFailure.deltaFlagTop (merge void t) :=
    h _ _ hstep
  simp [FlagFailure.deltaFlagTop, t] at hlt

/-! ## Constellation / structural hybrid barrier -/

/-- Constellation-size cannot strictly decrease on all `rec_succ` instances. -/
theorem no_constellation_strict_drop_rec_succ :
    ¬ (∀ (b s n : Trace),
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (app s (recΔ b s n))) <
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (recΔ b s (delta n)))) := by
  intro h
  have hlt := h void void void
  have hs :
      ConstellationFailure.constellationSize
        (ConstellationFailure.toConstellation (void : Trace)) ≥ 1 := by
    simp [ConstellationFailure.constellationSize, ConstellationFailure.toConstellation]
  have hge :=
    ConstellationFailure.constellation_size_not_decreasing void void void hs
  exact Nat.not_lt_of_ge hge hlt

/-- Constellation-size cannot globally orient full `Step`. -/
theorem no_global_step_orientation_constellation :
    ¬ GlobalOrients
      (fun t =>
        ConstellationFailure.constellationSize
          (ConstellationFailure.toConstellation t))
      (· < ·) := by
  intro h
  apply no_constellation_strict_drop_rec_succ
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-- Strictly monotone post-processing cannot rescue additive `simpleSize` on full `Step`. -/
theorem no_global_step_orientation_simpleSize_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ¬ GlobalOrients
      (fun t => f (UncheckedRecursionFailure.simpleSize t))
      (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta void)) (app void (recΔ void void void)) :=
    Step.R_rec_succ void void void
  have hlt :
      f (UncheckedRecursionFailure.simpleSize (app void (recΔ void void void))) <
      f (UncheckedRecursionFailure.simpleSize (recΔ void void (delta void))) :=
    h hstep
  have hge :
      UncheckedRecursionFailure.simpleSize (app void (recΔ void void void)) ≥
      UncheckedRecursionFailure.simpleSize (recΔ void void (delta void)) :=
    UncheckedRecursionFailure.rec_succ_additive_barrier void void void
  have hmono :
      f (UncheckedRecursionFailure.simpleSize (recΔ void void (delta void))) ≤
      f (UncheckedRecursionFailure.simpleSize (app void (recΔ void void void))) :=
    hf.monotone hge
  exact Nat.not_lt_of_ge hmono hlt

/-! ## Flag barrier (GlobalOrients form) -/

/-- A single top-level δ-flag cannot globally orient full `Step` (GlobalOrients form). -/
theorem no_global_step_orientation_flag :
    ¬ GlobalOrients FlagFailure.deltaFlagTop (· < ·) := by
  intro h
  have hstep : Step (merge void (delta void)) (delta void) :=
    Step.R_merge_void_left (delta void)
  have hlt := h hstep
  simp [FlagFailure.deltaFlagTop] at hlt

/-! ## Strict increase witness (rec_succ makes additive measures grow) -/

/-- Under the stated lower bound on `s`, `simpleSize` strictly increases across
`rec_succ`. -/
theorem rec_succ_size_strictly_increases (b s n : Trace)
    (hs : UncheckedRecursionFailure.simpleSize s ≥ 1) :
    UncheckedRecursionFailure.simpleSize (app s (recΔ b s n)) >
    UncheckedRecursionFailure.simpleSize (recΔ b s (delta n)) :=
  UncheckedRecursionFailure.rec_succ_size_increases b s n hs

/-! ## StrictMono generalization for kappa -/

/-- Strictly monotone post-processing cannot rescue `kappa` on full `Step`.
Analogous to `no_global_step_orientation_simpleSize_strictMono`. -/
theorem no_global_step_orientation_kappa_strictMono
    (f : Nat → Nat) (hf : StrictMono f) :
    ¬ GlobalOrients (fun t => f (FailedMeasures.kappa t)) (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta (delta void)))
      (app void (recΔ void void (delta void))) :=
    Step.R_rec_succ void void (delta void)
  have hlt := h hstep
  have hge : FailedMeasures.kappa (app void (recΔ void void (delta void))) ≥
      FailedMeasures.kappa (recΔ void void (delta (delta void))) := by
    simp [FailedMeasures.kappa]
  exact Nat.not_lt_of_ge (hf.monotone hge) hlt

/-! ## Dual-barrier theorem (rec_succ vs merge_void are complementary) -/

/-- Two concrete measures fail on different full-`Step` rules: `simpleSize` does not
decrease on `rec_succ`, while `deltaFlagTop` increases on `merge_void_left`. This
conjunction records both witnesses; it does not quantify over arbitrary measures. -/
theorem dual_barrier_rec_succ_and_merge_void :
    -- (1) Additive size fails on rec_succ:
    (∀ (b s n : Trace),
      UncheckedRecursionFailure.simpleSize (app s (recΔ b s n)) ≥
      UncheckedRecursionFailure.simpleSize (recΔ b s (delta n)))
    ∧
    -- (2) δ-flag increases on merge_void_left:
    (FlagFailure.deltaFlagTop (delta void) >
     FlagFailure.deltaFlagTop (merge void (delta void))) := by
  constructor
  · exact UncheckedRecursionFailure.rec_succ_additive_barrier
  · simp [FlagFailure.deltaFlagTop]

/-! ## Structural depth barrier

A nesting-depth measure that does not count `merge` as a level ties on
`merge_cancel`. -/

/-- Nesting depth where `merge` does not add a level. -/
@[simp] def nestingDepth : Trace → Nat
  | .void => 0
  | .delta t => nestingDepth t + 1
  | .integrate t => nestingDepth t + 1
  | .merge a b => max (nestingDepth a) (nestingDepth b)
  | .app a b => max (nestingDepth a) (nestingDepth b) + 1
  | .recΔ b s n => max (max (nestingDepth b) (nestingDepth s)) (nestingDepth n) + 1
  | .eqW a b => max (nestingDepth a) (nestingDepth b) + 1

/-- `nestingDepth` ties on `merge_cancel`: `nestingDepth (merge t t) = nestingDepth t`.
Since `merge t t → t`, strict orientation would require `nestingDepth t < nestingDepth t`. -/
theorem nestingDepth_merge_cancel_tie (t : Trace) :
    nestingDepth (merge t t) = nestingDepth t := by
  simp

/-- `nestingDepth` cannot globally orient full `Step` (fails at merge_cancel). -/
theorem no_global_step_orientation_nestingDepth :
    ¬ GlobalOrients nestingDepth (· < ·) := by
  intro h
  have hstep : Step (merge void void) void := Step.R_merge_cancel void
  have hlt := h hstep
  simp [nestingDepth] at hlt

/-! ## A multiplicative polynomial schema that ties on `rec_succ`

The concrete schema below assigns additive interpretations to `app` and a
multiplicative interpretation to `recΔ`:

  M(recΔ b s (delta n)) = M(b) + M(s)*(M(n)+1) = M(b) + M(s)*M(n) + M(s)
  M(app s (recΔ b s n)) = M(s) + M(b) + M(s)*M(n)

These values are equal by arithmetic normalization for every base weight `w`.
The theorem concerns this `polyMul` schema only; it is not a no-go theorem for
all polynomial interpretations. -/

/-- Polynomial measure with multiplicative `recΔ`, parameterized by base weight `w`. -/
@[simp] def polyMul (w : Nat) : Trace → Nat
  | .void => w
  | .delta t => polyMul w t + 1
  | .integrate t => polyMul w t + 1
  | .merge a b => polyMul w a + polyMul w b
  | .app a b => polyMul w a + polyMul w b
  | .recΔ b s n => polyMul w b + polyMul w s * polyMul w n
  | .eqW a b => polyMul w a + polyMul w b

/-- `polyMul` ties on `rec_succ` for every base weight. This is an exact equality,
not merely a non-strict inequality. -/
theorem poly_mul_ties_rec_succ (w : Nat) (b s n : Trace) :
    polyMul w (app s (recΔ b s n)) =
    polyMul w (recΔ b s (delta n)) := by
  simp [polyMul, Nat.mul_add]
  omega

/-- Polynomial `polyMul` cannot globally orient full `Step` (ties on rec_succ). -/
theorem no_global_step_orientation_polyMul (w : Nat) :
    ¬ GlobalOrients (polyMul w) (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta void)) (app void (recΔ void void void)) :=
    Step.R_rec_succ void void void
  have hlt := h hstep
  have heq := poly_mul_ties_rec_succ w void void void
  omega

/-! ## Unit-node cardinality barrier

`nodeCount` models the cardinality of a bag in which every constructor has unit
weight. It is not a formalization of the Dershowitz-Manna multiset order. Under
`rec_succ`, the duplicated `s` contributes an additional `nodeCount s`, so this
cardinality measure cannot strictly decrease. -/

/-- Node count: number of constructor applications in the term.
This represents a naive multiset measure where every node has weight 1
and the multiset is compared by cardinality (= sum of weights). -/
@[simp] def nodeCount : Trace → Nat
  | .void => 1
  | .delta t => nodeCount t + 1
  | .integrate t => nodeCount t + 1
  | .merge a b => nodeCount a + nodeCount b + 1
  | .app a b => nodeCount a + nodeCount b + 1
  | .recΔ b s n => nodeCount b + nodeCount s + nodeCount n + 1
  | .eqW a b => nodeCount a + nodeCount b + 1

/-- Naive multiset (node count) does not strictly decrease on `rec_succ`.
The duplication of `s` adds `nodeCount s` to the RHS, yielding ≥. -/
theorem nodeCount_rec_succ_barrier (b s n : Trace) :
    nodeCount (app s (recΔ b s n)) ≥ nodeCount (recΔ b s (delta n)) := by
  simp [nodeCount]
  omega

/-- Under the stated lower bound on `s`, node count strictly increases on `rec_succ`. -/
theorem nodeCount_rec_succ_increases (b s n : Trace)
    (hs : nodeCount s ≥ 2) :
    nodeCount (app s (recΔ b s n)) > nodeCount (recΔ b s (delta n)) := by
  simp [nodeCount]
  omega

/-- Node count cannot globally orient full `Step` (fails at rec_succ). -/
theorem no_global_step_orientation_nodeCount :
    ¬ GlobalOrients nodeCount (· < ·) := by
  intro h
  have hstep : Step (recΔ void void (delta void)) (app void (recΔ void void void)) :=
    Step.R_rec_succ void void void
  have hlt := h hstep
  have hge := nodeCount_rec_succ_barrier void void void
  omega

/-! ## Isolated path-order components

Scope note: this file does not show that full Lexicographic Path Ordering (LPO)
or Multiset Path Ordering (MPO) fails to orient the KO7 calculus. Both full LPO and
full MPO *succeed* in orienting the unrestricted system: LPO is CeTA-certified (external),
and MPO orientation is Lean-mechanized in `Meta/MPO_FullStep.lean` (`mpo_orients_step`).

The following theorems instead isolate two weaker components: a pure head-rank
measure and a precedence-free additive weight. Their failure does not establish
a necessity theorem for any particular feature of full LPO or MPO.
-/

/-! ## Pure head-precedence barrier

A measure that relies strictly on the precedence of the head constructor
cannot orient collapsing rules like `merge_cancel`, because the RHS can
have the same head constructor as the LHS.
-/

inductive OpHead | void | delta | integrate | merge | app | recΔ | eqW

def getHead : Trace → OpHead
  | .void => .void
  | .delta _ => .delta
  | .integrate _ => .integrate
  | .merge _ _ => .merge
  | .app _ _ => .app
  | .recΔ _ _ _ => .recΔ
  | .eqW _ _ => .eqW

def headPrecedenceMeasure (rank : OpHead → Nat) : Trace → Nat :=
  fun t => rank (getHead t)

/-- Pure head precedence cannot globally orient `Step` (fails at merge_cancel). -/
theorem no_global_step_orientation_headPrecedence (rank : OpHead → Nat) :
    ¬ GlobalOrients (headPrecedenceMeasure rank) (· < ·) := by
  intro h
  have hstep : Step (merge (merge void void) (merge void void)) (merge void void) :=
    Step.R_merge_cancel (merge void void)
  have hlt := h hstep
  revert hlt
  simp [headPrecedenceMeasure, getHead]

/-! ## Linear weight barrier without precedence

A purely additive weight function, where each constructor adds a fixed constant
to the sum of its arguments' weights, cannot globally orient `Step`. This result
concerns the isolated additive-weight component, not full Knuth-Bendix Order.
-/

def linearWeight (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat) : Trace → Nat
  | .void => c_void
  | .delta t => c_delta + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq t
  | .integrate t => c_int + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq t
  | .merge a b => c_merge + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b
  | .app a b => c_app + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b
  | .recΔ b s n => c_rec + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq s + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq n
  | .eqW a b => c_eq + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq a + linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq b

/-- No linear weight function can globally orient `Step` (fails at rec_succ). -/
theorem no_global_step_orientation_linearWeight (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat) :
    ¬ GlobalOrients (linearWeight c_void c_delta c_int c_merge c_app c_rec c_eq) (· < ·) := by
  intro h
  have h1 := h (Step.R_rec_succ void void void)
  have h2 := h (Step.R_rec_succ void (delta void) void)
  simp [linearWeight] at h1 h2
  omega

/-! ## Standard Tree Depth Barrier

A standard tree depth measure (where every constructor adds 1 to the maximum
depth of its arguments) cannot globally orient `Step` because the duplication
of `s` in `rec_succ` can strictly increase the overall depth of the term.
-/

@[simp] def treeDepth : Trace → Nat
  | .void => 0
  | .delta t => treeDepth t + 1
  | .integrate t => treeDepth t + 1
  | .merge a b => max (treeDepth a) (treeDepth b) + 1
  | .app a b => max (treeDepth a) (treeDepth b) + 1
  | .recΔ b s n => max (max (treeDepth b) (treeDepth s)) (treeDepth n) + 1
  | .eqW a b => max (treeDepth a) (treeDepth b) + 1

/-- Standard tree depth strictly increases on `rec_succ` under the stated depth condition. -/
theorem treeDepth_rec_succ_increases (b s n : Trace)
    (hs : treeDepth s > treeDepth n + 1) :
    treeDepth (app s (recΔ b s n)) > treeDepth (recΔ b s (delta n)) := by
  simp [treeDepth]
  omega

/-- Standard tree depth cannot globally orient `Step`. -/
theorem no_global_step_orientation_treeDepth :
    ¬ GlobalOrients treeDepth (· < ·) := by
  intro h
  -- Let n = void (depth 0). Let s = delta (delta void) (depth 2).
  have hstep : Step (recΔ void (delta (delta void)) (delta void))
                    (app (delta (delta void)) (recΔ void (delta (delta void)) void)) :=
    Step.R_rec_succ void (delta (delta void)) void
  have hlt := h hstep
  -- LHS depth is 3. RHS depth is 4. 3 < 4 contradicts orientation.
  simp [treeDepth] at hlt

/-! ## Full-step witness (duplication branch is present in kernel Step) -/

/-- The unrestricted kernel `Step` contains the duplication branch explicitly. -/
theorem full_step_has_rec_succ_instance :
    ∃ b s n, Step (recΔ b s (delta n)) (app s (recΔ b s n)) :=
  UncheckedRecursionFailure.full_step_permits_barrier

end OperatorKO7.MetaConjectureBoundary
